from fastapi import APIRouter, BackgroundTasks
from api.app.schemas import replay as replay_schema
from pydantic import BaseModel
import uuid
from api.app import replay

router = APIRouter()


class ReplayReport(BaseModel):
    status: str
    diff: dict


@router.post("/{execution_id}", response_model=ReplayReport, status_code=202)
async def create_replay(
    *,
    execution_id: uuid.UUID,
    replay_in: replay_schema.ReplayCreate,
    background_tasks: BackgroundTasks,
):
    """
    Create new replay for an execution.
    """
    background_tasks.add_task(
        replay.run_replay, execution_id=execution_id, replay_config=replay_in
    )
    return ReplayReport(status="STARTED", diff={})
