import logging

from fastapi import APIRouter, HTTPException, Request, Depends, Path, Query
import redis
from rq import Queue

from app.schemas.clone import CloneRequest, CloneResponse, CloneHistoryResponse
from app.schemas.job import StatusResponse
from app.api.controllers import clone_controller, artifact_controller

logger = logging.getLogger(__name__)
router = APIRouter()


# --- Dependencies ---
def get_redis_conn(request: Request) -> redis.Redis:
    if (
        not hasattr(request.app.state, "redis_conn")
        or request.app.state.redis_conn is None
    ):
        logger.error("Redis connection not available in app state.")
        raise HTTPException(status_code=503, detail="Redis service unavailable")
    return request.app.state.redis_conn


def get_rq_queue(request: Request) -> Queue:
    if not hasattr(request.app.state, "rq_queue") or request.app.state.rq_queue is None:
        logger.error("RQ queue not available in app state.")
        raise HTTPException(status_code=503, detail="RQ service unavailable")
    return request.app.state.rq_queue


@router.post(
    "/clone",
    response_model=CloneResponse,
    summary="Submit a URL for cloning",
    tags=["Cloning"],
)
async def enqueue_clone_job(
    payload: CloneRequest,
    redis_conn: redis.Redis = Depends(get_redis_conn),
    rq_queue: Queue = Depends(get_rq_queue),
):
    return clone_controller.enqueue_clone_job(payload, redis_conn, rq_queue)


@router.get(
    "/status/{job_id}",
    response_model=StatusResponse,
    summary="Get the status of a cloning job",
    tags=["Cloning"],
)
async def get_job_status(
    job_id: str = Path(..., description="The ID of the job to check."),
    redis_conn: redis.Redis = Depends(get_redis_conn),
):
    return clone_controller.get_job_status(job_id, redis_conn)


@router.get(
    "/artifact/{object_key:path}",
    summary="Get a pre-signed URL for a cloned artifact",
    tags=["Artifacts"],
)
async def get_artifact_url(
    object_key: str = Path(
        ...,
        description="The key (path) of the artifact in MinIO. e.g., 'some_hash.liquid' or 'job_id/screenshot.png'",
    ),
):
    return artifact_controller.get_artifact_url(object_key)


@router.get(
    "/clones/history",
    response_model=CloneHistoryResponse,
    summary="List previously cloned Liquid artifacts",
    tags=["Artifacts"],
)
async def get_clone_history(
    limit: int = Query(
        20, ge=1, le=100, description="Maximum number of history items to return."
    )
):
    """
    Retrieves a list of previously cloned Liquid artifacts from MinIO.
    Returns the object key, a pre-signed URL to view it, last modified timestamp, and size.
    """
    return artifact_controller.get_clone_history(limit)
