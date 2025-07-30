import uuid
import enum
from sqlalchemy import Column, Enum, ForeignKey, String
from sqlalchemy.dialects.postgresql import UUID, TIMESTAMP, JSONB
from api.app.db.base_class import Base


class ExecutionStatus(str, enum.Enum):
    PENDING = "PENDING"
    RUNNING = "RUNNING"
    COMPLETED = "COMPLETED"
    FAILED = "FAILED"


class Execution(Base):
    __tablename__ = "executions"

    id = Column(UUID(as_uuid=True), primary_key=True, default=uuid.uuid4)
    run_id = Column(String, unique=True, index=True, nullable=False)
    command = Column(JSONB, nullable=True)
    git_sha = Column(String, nullable=True)
    cwd = Column(String, nullable=True)
    workflow_id = Column(UUID(as_uuid=True), ForeignKey("workflows.id"), nullable=False)
    status = Column(
        Enum(ExecutionStatus), default=ExecutionStatus.PENDING, nullable=False
    )
    started_at = Column(TIMESTAMP)
    finished_at = Column(TIMESTAMP)
