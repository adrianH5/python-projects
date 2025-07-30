from sqlalchemy.orm import Session
from api.app.crud.base import CRUDBase
from api.app.models.workflow import Workflow
from api.app.schemas.workflow import WorkflowCreate, WorkflowUpdate


class CRUDWorkflow(CRUDBase[Workflow, WorkflowCreate, WorkflowUpdate]):
    def get_by_name(self, db: Session, *, name: str) -> Workflow | None:
        return db.query(Workflow).filter(Workflow.name == name).first()

    def delete_all(self, db: Session) -> int:
        """Deletes all workflows from the database."""
        num_rows_deleted = db.query(self.model).delete()
        db.commit()
        return num_rows_deleted


workflow = CRUDWorkflow(Workflow)
