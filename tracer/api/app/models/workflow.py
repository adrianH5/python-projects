import uuid
from sqlalchemy import Column, String, func
from sqlalchemy.dialects.postgresql import UUID, JSONB, TIMESTAMP
from api.app.db.base_class import Base


class Workflow(Base):
    __tablename__ = "workflows"

    id = Column(UUID(as_uuid=True), primary_key=True, default=uuid.uuid4)
    name = Column(String, unique=True, index=True, nullable=False)
    spec = Column(JSONB)
    created_at = Column(TIMESTAMP, default=func.now(), nullable=False)
