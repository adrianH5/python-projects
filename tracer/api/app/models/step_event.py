from sqlalchemy import Column, BigInteger, Integer, String, Text, ForeignKey, func
from sqlalchemy.dialects.postgresql import JSONB, TIMESTAMP
from api.app.db.base_class import Base


class StepEvent(Base):
    __tablename__ = "step_events"

    id = Column(BigInteger, primary_key=True, autoincrement=True)
    execution_id = Column(ForeignKey("executions.id"), nullable=False)
    idx = Column(Integer, nullable=False)
    service = Column(String, nullable=False)
    endpoint = Column(String, nullable=False)
    request = Column(JSONB)
    response = Column(JSONB)
    latency_ms = Column(Integer)
    error = Column(Text)
    sha256 = Column(String(64))
    ts = Column(TIMESTAMP, default=func.now(), nullable=False)
