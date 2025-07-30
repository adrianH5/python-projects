import uuid
from fastapi import APIRouter, Depends, HTTPException
from sqlalchemy.orm import Session
from api.app import crud
from api.app.schemas import workflow as workflow_schema, execution as execution_schema
from api.app.db.session import get_db
from typing import List

router = APIRouter()


@router.get("/", response_model=List[workflow_schema.Workflow])
def read_workflows(
    db: Session = Depends(get_db),
    skip: int = 0,
    limit: int = 100,
):
    """
    Retrieve workflows.
    """
    workflows = crud.workflow.get_multi(db, skip=skip, limit=limit)
    return workflows


@router.post("/", response_model=workflow_schema.Workflow, status_code=201)
def create_workflow(
    *,
    db: Session = Depends(get_db),
    workflow_in: workflow_schema.WorkflowCreate,
):
    """
    Create new workflow.
    """
    workflow = crud.workflow.create(db=db, obj_in=workflow_in)
    return workflow


@router.get("/{workflow_id}", response_model=workflow_schema.Workflow)
def read_workflow(
    *,
    db: Session = Depends(get_db),
    workflow_id: uuid.UUID,
):
    """
    Get workflow by ID.
    """
    workflow = crud.workflow.get(db=db, id=workflow_id)
    if not workflow:
        raise HTTPException(status_code=404, detail="Workflow not found")
    return workflow


@router.get(
    "/{workflow_id}/executions", response_model=List[execution_schema.Execution]
)
def read_workflow_executions(
    *,
    db: Session = Depends(get_db),
    workflow_id: uuid.UUID,
    skip: int = 0,
    limit: int = 100,
):
    """
    Get executions for a specific workflow.
    """
    workflow = crud.workflow.get(db=db, id=workflow_id)
    if not workflow:
        raise HTTPException(status_code=404, detail="Workflow not found")
    executions = crud.execution.get_multi_by_workflow(
        db=db, workflow_id=workflow_id, skip=skip, limit=limit
    )
    return executions


@router.delete("/", status_code=200)
def delete_all_workflows(
    db: Session = Depends(get_db),
):
    """
    Delete all workflows and their associated data.
    """
    deleted_count = crud.workflow.delete_all(db=db)
    return {"message": f"Successfully deleted {deleted_count} workflows."}
