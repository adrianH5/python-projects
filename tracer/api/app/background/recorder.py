"""
Background worker for processing trace events from Redis stream.

This module consumes trace events from a Redis stream and persists them
to the database, organizing them into workflows, executions, and steps.
"""

import asyncio
import json
import logging
from typing import Dict, List, Optional, Tuple
from urllib.parse import urlparse

import redis.asyncio as redis
from redis import ResponseError
from sqlalchemy.orm import Session

from api.app import crud, schemas
from api.app.core.config import settings
from api.app.db.session import SessionLocal

logger = logging.getLogger(__name__)


class TraceEventProcessor:
    """Processes trace events and persists them to the database."""

    def __init__(self, db: Session):
        self.db = db

    def process_event(self, trace_event: Dict) -> None:
        """
        Process a single trace event.

        Args:
            trace_event: Dictionary containing trace event data
        """
        workflow_name = trace_event["workflow_name"]
        run_id = trace_event["run_id"]

        workflow = self._get_or_create_workflow(workflow_name)
        execution = self._get_or_create_execution(workflow.id, run_id, trace_event)

        if self._is_completion_event(trace_event):
            self._mark_execution_completed(execution)
        elif self._is_step_event(trace_event):
            self._create_step_event(execution, trace_event)

    def _get_or_create_workflow(self, workflow_name: str):
        """Get existing workflow or create new one."""
        workflow = crud.workflow.get_by_name(self.db, name=workflow_name)

        if workflow is None:
            logger.info(f"Creating new workflow: {workflow_name}")
            workflow_data = schemas.workflow.WorkflowCreate(name=workflow_name)
            workflow = crud.workflow.create(self.db, obj_in=workflow_data, commit=False)
            logger.info(f"Created workflow with ID: {workflow.id}")
        else:
            logger.info(f"Found existing workflow with ID: {workflow.id}")

        return workflow

    def _get_or_create_execution(
        self, workflow_id: int, run_id: str, trace_event: Dict
    ):
        """Get existing execution or create new one."""
        logger.info(
            f"Getting or creating execution for workflow ID: {workflow_id} "
            f"and run ID: {run_id}"
        )

        execution = crud.execution.get_or_create(
            self.db,
            workflow_id=workflow_id,
            run_id=run_id,
            command=trace_event.get("command"),
            git_sha=trace_event.get("git_sha"),
            cwd=trace_event.get("cwd"),
            commit=False,
        )

        logger.info(f"Using execution with ID: {execution.id}")
        return execution

    def _is_completion_event(self, trace_event: Dict) -> bool:
        """Check if event marks execution completion."""
        return trace_event.get("status") == "COMPLETED"

    def _is_step_event(self, trace_event: Dict) -> bool:
        """Check if event contains step data."""
        return "request" in trace_event and "response" in trace_event

    def _mark_execution_completed(self, execution) -> None:
        """Mark execution as completed."""
        logger.info(f"Updating execution {execution.id} to status COMPLETED")
        execution.status = "COMPLETED"
        self.db.add(execution)

    def _create_step_event(self, execution, trace_event: Dict) -> None:
        """Create a new step event from trace data."""
        endpoint = self._extract_endpoint(trace_event["request"]["url"])
        next_idx = self._get_next_step_index(execution.id)

        step_event_data = schemas.step_event.StepEventCreate(
            execution_id=execution.id,
            idx=next_idx,
            service=trace_event["service_name"],
            endpoint=endpoint,
            request=trace_event["request"],
            response=trace_event["response"],
            latency_ms=trace_event.get("latency_ms"),
        )

        logger.info(f"Creating step event: {step_event_data}")
        crud.step_event.create(self.db, obj_in=step_event_data, commit=False)

    def _extract_endpoint(self, url: str) -> str:
        """Extract endpoint path from URL."""
        parsed_url = urlparse(url)
        return parsed_url.path

    def _get_next_step_index(self, execution_id: int) -> int:
        """Get the next sequential index for a step."""
        last_step = crud.step_event.get_last_by_execution(
            self.db, execution_id=execution_id
        )
        return (last_step.idx + 1) if last_step else 0


class RedisStreamConsumer:
    """Manages Redis stream consumption for trace events."""

    STREAM_NAME = "trace.events"
    GROUP_NAME = "recorder_group"
    CONSUMER_NAME = "recorder_consumer"
    BATCH_SIZE = 100
    BLOCK_TIMEOUT_MS = 5000

    def __init__(self, redis_client: redis.Redis):
        self.redis_client = redis_client

    async def ensure_consumer_group(self) -> None:
        """Ensure the consumer group exists."""
        try:
            await self.redis_client.xgroup_create(
                self.STREAM_NAME, self.GROUP_NAME, id="0", mkstream=True
            )
        except ResponseError as e:
            if "BUSYGROUP" not in str(e):
                raise

    async def read_messages(self) -> Optional[List[Tuple[str, List]]]:
        """Read messages from the stream."""
        logger.info("Waiting for messages...")

        try:
            messages = await self.redis_client.xreadgroup(
                self.GROUP_NAME,
                self.CONSUMER_NAME,
                {self.STREAM_NAME: ">"},
                count=self.BATCH_SIZE,
                block=self.BLOCK_TIMEOUT_MS,
            )
            return messages
        except (asyncio.CancelledError, GeneratorExit):
            logger.info("Recorder worker cancelled. Shutting down gracefully.")
            raise

    async def acknowledge_message(self, message_id: str) -> None:
        """Acknowledge successful message processing."""
        await self.redis_client.xack(self.STREAM_NAME, self.GROUP_NAME, message_id)


async def process_message_batch(
    consumer: RedisStreamConsumer, messages: List[Tuple[str, List]]
) -> None:
    """Process a batch of messages from Redis."""
    db = SessionLocal()
    processor = TraceEventProcessor(db)

    try:
        for _, message_list in messages:
            for message_id, data in message_list:
                logger.info(f"Processing message {message_id}")

                trace_event = json.loads(data["data"])
                processor.process_event(trace_event)

                await consumer.acknowledge_message(message_id)

        logger.info("Committing transaction.")
        db.commit()
        logger.info("Transaction committed.")
    finally:
        db.close()


async def recorder_worker() -> None:
    """
    Background worker that consumes trace events from Redis.

    Continuously reads trace events from a Redis stream and persists
    them to the database, organizing them into workflows and executions.
    """
    try:
        redis_client = redis.from_url(settings.REDIS_URL, decode_responses=True)
        consumer = RedisStreamConsumer(redis_client)

        await consumer.ensure_consumer_group()

        while True:
            try:
                messages = await consumer.read_messages()

                if not messages:
                    continue

                logger.info(f"Received {len(messages)} messages from Redis.")
                await process_message_batch(consumer, messages)

            except (asyncio.CancelledError, GeneratorExit):
                break
            except Exception as e:
                logger.error(f"Error in recorder worker: {e}", exc_info=True)

                if _is_event_loop_error(e):
                    logger.warning("Event loop not running. Exiting worker.")
                    break

                await asyncio.sleep(5)

    except Exception as e:
        logger.error(f"Critical error in recorder worker startup: {e}", exc_info=True)


def _is_event_loop_error(exception: Exception) -> bool:
    """Check if exception is due to missing event loop."""
    return isinstance(exception, RuntimeError) and "no running event loop" in str(
        exception
    )
