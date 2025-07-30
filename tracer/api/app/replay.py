import asyncio
import os
import socket
import uuid

import docker

from .db.session import SessionLocal
from . import crud
from .models.execution import ExecutionStatus
from .models.step_event import StepEvent
from .schemas import execution
from .schemas.replay import ReplayCreate


async def run_replay(execution_id: uuid.UUID, replay_config: ReplayCreate):
    """
    Main function to run a replay for a given execution.
    It creates a new execution record in the database to represent the replay,
    then re-executes the original command in a controlled environment.
    """
    print(
        f"Starting replay for original execution {execution_id} with mode: {replay_config.mode}"
    )

    db = SessionLocal()
    replay_execution = None
    try:
        original_execution = crud.execution.get(db=db, id=execution_id)
        if not original_execution:
            print(f"ERROR: Original execution {execution_id} not found.")
            return

        # Create a new execution record for this replay.
        execution_in = execution.ExecutionCreate(
            workflow_id=original_execution.workflow_id,
            run_id=f"replay-{uuid.uuid4()}",
            status=ExecutionStatus.PENDING,
        )
        replay_execution = crud.execution.create(db=db, obj_in=execution_in)
        replay_execution.status = ExecutionStatus.RUNNING
        db.add(replay_execution)
        db.commit()
        db.refresh(replay_execution)
        print(f"Created new execution {replay_execution.id} for replay.")

        client = docker.from_env()
        loop = asyncio.get_running_loop()

        try:
            hostname = socket.gethostname()
            current_container = client.containers.get(hostname)
            image_name = current_container.image.tags[0]
            network_name = list(
                current_container.attrs["NetworkSettings"]["Networks"].keys()
            )[0]
            project_name = network_name.split("_")[0]
            proxy_image_name = f"{project_name}-sdk-proxy"
        except (docker.errors.NotFound, IndexError) as e:
            print(
                f"ERROR: Could not determine current container's image and network: {e}. Falling back to defaults."
            )
            image_name = "tracelab-api"  # Fallback
            network_name = "tracelab_default"  # Fallback
            proxy_image_name = "tracelab-sdk-proxy"  # Fallback

        if not original_execution.command:
            raise ValueError("Original execution has no command to replay.")

        command_to_run = ["python"] + list(original_execution.command)

        workflow = crud.workflow.get(db, id=original_execution.workflow_id)
        if not workflow:
            raise ValueError(f"Workflow {original_execution.workflow_id} not found.")

        first_step = (
            db.query(StepEvent)
            .filter(StepEvent.execution_id == original_execution.id)
            .order_by(StepEvent.idx.asc())
            .first()
        )
        service_name = first_step.service if first_step else "default-service"

        proxy_env = {
            "REDIS_URL": os.environ.get("REDIS_URL", "redis://redis:6379/0"),
            "TRACELAB_WORKFLOW_NAME": workflow.name,
            "TRACELAB_SERVICE_NAME": service_name,
            "TRACELAB_RUN_ID": replay_execution.run_id,
        }

        proxy_container_name = f"sdk-proxy-replay-{replay_execution.id}"
        proxy_container = None

        try:
            print(
                f"Starting dedicated proxy container '{proxy_container_name}' with image '{proxy_image_name}'..."
            )
            proxy_container = await loop.run_in_executor(
                None,
                lambda: client.containers.run(
                    image=proxy_image_name,
                    name=proxy_container_name,
                    environment=proxy_env,
                    network=network_name,
                    detach=True,
                ),
            )

            command_env = os.environ.copy()
            command_env.pop("HTTP_PROXY", None)
            command_env.pop("HTTPS_PROXY", None)
            command_env["HTTP_PROXY"] = f"http://{proxy_container_name}:8888"
            command_env["HTTPS_PROXY"] = f"http://{proxy_container_name}:8888"

            print(f"Starting replay command container with image '{image_name}'...")
            print(f"Re-running command: {' '.join(command_to_run)} in /app")

            # Run the replay command in a container. This is a blocking call,
            # so it's run in a thread to avoid holding up the asyncio event loop.
            await loop.run_in_executor(
                None,
                lambda: client.containers.run(
                    image=image_name,
                    command=command_to_run,
                    working_dir="/app",
                    environment=command_env,
                    network=network_name,
                    remove=True,
                    detach=False,
                ),
            )
            print(
                f"Replay container finished successfully for execution {replay_execution.id}."
            )
            replay_execution.status = ExecutionStatus.COMPLETED

        except docker.errors.ContainerError as e:
            print(f"Replay container failed for execution {replay_execution.id}.")
            print(f"Error: {e}")
            replay_execution.status = ExecutionStatus.FAILED
        finally:
            if proxy_container:
                print(
                    f"Stopping and removing proxy container '{proxy_container_name}'..."
                )
                await loop.run_in_executor(None, proxy_container.stop)
                await loop.run_in_executor(None, proxy_container.remove)

        db.add(replay_execution)
        db.commit()
        db.refresh(replay_execution)

    except Exception as e:
        print(f"ERROR during replay of execution {execution_id}: {e}")
        if replay_execution:
            replay_execution.status = ExecutionStatus.FAILED
            db.add(replay_execution)
            db.commit()
            db.refresh(replay_execution)
            print(f"Replay execution {replay_execution.id} marked as FAILED.")
    finally:
        db.close()
