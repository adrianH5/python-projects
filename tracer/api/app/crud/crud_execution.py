from sqlalchemy.orm import Session
from api.app.crud.base import CRUDBase
from api.app.models.execution import Execution
from api.app.schemas.execution import ExecutionCreate, ExecutionUpdate
import uuid
from typing import List, Optional


class CRUDExecution(CRUDBase[Execution, ExecutionCreate, ExecutionUpdate]):
    def get_or_create(
        self,
        db: Session,
        *,
        workflow_id: uuid.UUID,
        run_id: str,
        command: Optional[List[str]] = None,
        git_sha: Optional[str] = None,
        cwd: Optional[str] = None,
        commit: bool = True
    ) -> Execution:
        """
        Get an execution by its run_id, or create a new one if it doesn't exist.
        """
        execution = db.query(Execution).filter(Execution.run_id == run_id).first()
        if not execution:
            execution_in = ExecutionCreate(
                workflow_id=workflow_id,
                run_id=run_id,
                command=command,
                git_sha=git_sha,
                cwd=cwd,
            )
            execution = self.create(db, obj_in=execution_in, commit=commit)
        else:
            # Backfill missing info if needed. This can happen if the first event
            # didn't have all the details for some reason.
            needs_commit = False
            if command and not execution.command:
                execution.command = command
                needs_commit = True
            if git_sha and not execution.git_sha:
                execution.git_sha = git_sha
                needs_commit = True
            if cwd and not execution.cwd:
                execution.cwd = cwd
                needs_commit = True

            if needs_commit:
                db.add(execution)
                if commit:
                    db.commit()
                    db.refresh(execution)
        return execution

    def get_multi_by_workflow(
        self, db: Session, *, workflow_id: uuid.UUID, skip: int = 0, limit: int = 100
    ) -> List[Execution]:
        return (
            db.query(self.model)
            .filter(Execution.workflow_id == workflow_id)
            .offset(skip)
            .limit(limit)
            .all()
        )


execution = CRUDExecution(Execution)
