"""
WebSocket endpoints for real-time event streaming.

This module provides WebSocket connections for clients to receive
live updates about execution events as they occur.
"""

import asyncio
import json
import logging
import uuid
from typing import Set

import redis.asyncio as redis
from fastapi import APIRouter, WebSocket, WebSocketDisconnect, Query

from api.app.core.config import settings

logger = logging.getLogger(__name__)

websocket_router = APIRouter()


class ConnectionManager:
    """Manages WebSocket connections and message broadcasting."""

    def __init__(self):
        self.active_connections: Set[WebSocket] = set()

    async def connect(self, websocket: WebSocket) -> None:
        """Accept and track a new WebSocket connection."""
        await websocket.accept()
        self.active_connections.add(websocket)
        logger.info(
            f"Client connected. Total connections: {len(self.active_connections)}"
        )

    def disconnect(self, websocket: WebSocket) -> None:
        """Remove a WebSocket connection from tracking."""
        self.active_connections.discard(websocket)
        logger.info(
            f"Client disconnected. Total connections: {len(self.active_connections)}"
        )

    async def send_json(self, websocket: WebSocket, data: dict) -> None:
        """Send JSON data to a specific WebSocket connection."""
        try:
            await websocket.send_json(data)
        except Exception as e:
            logger.error(f"Error sending message to client: {e}")
            self.disconnect(websocket)


manager = ConnectionManager()


@websocket_router.websocket("/ws/events")
async def websocket_endpoint(
    websocket: WebSocket, execution_id: uuid.UUID = Query(..., alias="exec")
) -> None:
    """
    WebSocket endpoint for streaming execution events.

    Args:
        websocket: WebSocket connection
        execution_id: UUID of the execution to monitor
    """
    await manager.connect(websocket)

    try:
        await stream_execution_events(websocket, execution_id)
    except WebSocketDisconnect:
        logger.info(f"Client disconnected from execution {execution_id}")
    except Exception as e:
        logger.error(f"Error in WebSocket connection: {e}")
    finally:
        manager.disconnect(websocket)


async def stream_execution_events(
    websocket: WebSocket, execution_id: uuid.UUID
) -> None:
    """
    Stream events for a specific execution to the WebSocket client.

    Args:
        websocket: WebSocket connection
        execution_id: UUID of the execution to monitor
    """
    redis_client = redis.from_url(settings.REDIS_URL, decode_responses=True)

    try:
        # Subscribe to execution-specific channel
        pubsub = redis_client.pubsub()
        channel_name = f"execution:{execution_id}:events"
        await pubsub.subscribe(channel_name)

        logger.info(f"Subscribed to channel: {channel_name}")

        # Send initial connection confirmation
        await manager.send_json(
            websocket,
            {
                "type": "connection",
                "status": "connected",
                "execution_id": str(execution_id),
            },
        )

        # Listen for messages
        async for message in pubsub.listen():
            if message["type"] == "message":
                try:
                    event_data = json.loads(message["data"])
                    await manager.send_json(websocket, event_data)
                except json.JSONDecodeError:
                    logger.error(f"Invalid JSON in message: {message['data']}")
                except Exception as e:
                    logger.error(f"Error processing message: {e}")

    finally:
        await pubsub.unsubscribe(channel_name)
        await redis_client.close()


@websocket_router.websocket("/ws/workflows/{workflow_id}/events")
async def workflow_events_endpoint(websocket: WebSocket, workflow_id: int) -> None:
    """
    WebSocket endpoint for streaming all events from a workflow.

    Args:
        websocket: WebSocket connection
        workflow_id: ID of the workflow to monitor
    """
    await manager.connect(websocket)

    try:
        # Send periodic heartbeat messages
        while True:
            await manager.send_json(
                websocket,
                {
                    "type": "heartbeat",
                    "workflow_id": workflow_id,
                    "timestamp": asyncio.get_event_loop().time(),
                },
            )
            await asyncio.sleep(30)

    except WebSocketDisconnect:
        logger.info(f"Client disconnected from workflow {workflow_id}")
    finally:
        manager.disconnect(websocket)
