from pydantic import BaseModel
import uuid
from datetime import datetime
from typing import Optional, Any


class WorkflowBase(BaseModel):
    name: str
    spec: Optional[Any] = None


class WorkflowCreate(WorkflowBase):
    pass


class WorkflowUpdate(WorkflowBase):
    pass


class WorkflowInDBBase(WorkflowBase):
    id: uuid.UUID
    created_at: datetime

    class Config:
        from_attributes = True


class Workflow(WorkflowInDBBase):
    pass
