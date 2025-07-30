from pydantic import BaseModel
import uuid
from datetime import datetime
from typing import Optional, Any


class StepEventBase(BaseModel):
    execution_id: uuid.UUID
    idx: int
    service: str
    endpoint: str
    request: Optional[Any] = None
    response: Optional[Any] = None
    latency_ms: Optional[int] = None
    error: Optional[str] = None
    sha256: Optional[str] = None


class StepEventCreate(StepEventBase):
    pass


class StepEventUpdate(BaseModel):
    pass


class StepEventInDBBase(StepEventBase):
    id: int
    ts: datetime

    class Config:
        from_attributes = True


class StepEvent(StepEventInDBBase):
    pass
