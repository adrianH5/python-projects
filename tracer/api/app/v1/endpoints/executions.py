from fastapi import APIRouter, Depends, HTTPException
from sqlalchemy.orm import Session
from api.app import crud
from api.app.schemas import (
    execution as execution_schema,
    step_event as step_event_schema,
)
from api.app.db.session import get_db
from typing import List, Any
import uuid

router = APIRouter()


@router.get("/", response_model=List[execution_schema.Execution])
def read_executions(
    db: Session = Depends(get_db),
    skip: int = 0,
    limit: int = 100,
    workflow_id: uuid.UUID = None,
):
    """
    Retrieve executions.
    """
    if workflow_id:
        executions = crud.execution.get_multi_by_workflow(
            db, workflow_id=workflow_id, skip=skip, limit=limit
        )
    else:
        executions = crud.execution.get_multi(db, skip=skip, limit=limit)
    return executions


@router.post("/", response_model=execution_schema.Execution, status_code=202)
def create_execution(
    *,
    db: Session = Depends(get_db),
    execution_in: execution_schema.ExecutionCreate,
) -> Any:
    """
    Create new execution.
    """
    execution = crud.execution.create(db=db, obj_in=execution_in)
    return execution


@router.get("/{execution_id}", response_model=execution_schema.Execution)
def read_execution(
    *,
    db: Session = Depends(get_db),
    execution_id: uuid.UUID,
) -> Any:
    """
    Get execution by ID.
    """
    execution = crud.execution.get(db=db, id=execution_id)
    if not execution:
        raise HTTPException(status_code=404, detail="Execution not found")
    return execution


@router.get("/{execution_id}/events", response_model=List[step_event_schema.StepEvent])
def read_execution_events(
    *,
    db: Session = Depends(get_db),
    execution_id: uuid.UUID,
    skip: int = 0,
    limit: int = 100,
) -> Any:
    """
    Get step events for an execution.
    """
    events = crud.step_event.get_multi_by_execution(
        db, execution_id=execution_id, skip=skip, limit=limit
    )
    return events
