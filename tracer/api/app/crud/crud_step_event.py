import uuid
from typing import List, Optional

from sqlalchemy.orm import Session

from api.app.crud.base import CRUDBase
from api.app.models.step_event import StepEvent
from api.app.schemas.step_event import StepEventCreate, StepEventUpdate


class CRUDStepEvent(CRUDBase[StepEvent, StepEventCreate, StepEventUpdate]):
    def get_last_by_execution(
        self, db: Session, *, execution_id: uuid.UUID
    ) -> Optional[StepEvent]:
        return (
            db.query(self.model)
            .filter(StepEvent.execution_id == execution_id)
            .order_by(StepEvent.idx.desc())
            .first()
        )

    def get_multi_by_execution(
        self, db: Session, *, execution_id: uuid.UUID, skip: int = 0, limit: int = 100
    ) -> List[StepEvent]:
        return (
            db.query(self.model)
            .filter(StepEvent.execution_id == execution_id)
            .order_by(StepEvent.idx)
            .offset(skip)
            .limit(limit)
            .all()
        )


step_event = CRUDStepEvent(StepEvent)
