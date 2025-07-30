from pydantic import BaseModel
import uuid
from datetime import datetime
from typing import Optional, List
from api.app.models.execution import ExecutionStatus


class ExecutionBase(BaseModel):
    workflow_id: uuid.UUID
    run_id: str
    command: Optional[List[str]] = None
    git_sha: Optional[str] = None
    cwd: Optional[str] = None
    status: Optional[ExecutionStatus] = ExecutionStatus.PENDING


class ExecutionCreate(ExecutionBase):
    pass


class ExecutionUpdate(BaseModel):
    status: Optional[ExecutionStatus] = None


class ExecutionInDBBase(ExecutionBase):
    id: uuid.UUID
    started_at: Optional[datetime] = None
    finished_at: Optional[datetime] = None

    class Config:
        from_attributes = True


class Execution(ExecutionInDBBase):
    pass
