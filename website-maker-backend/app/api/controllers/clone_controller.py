import uuid
import datetime
import logging

import redis
from rq import Queue
from fastapi import HTTPException
from pydantic import ValidationError

from app.schemas.clone import CloneRequest, CloneResponse
from app.schemas.job import StatusResponse, JobStatus
from app.domain.orchestrator import run_clone as run_clone_orchestrator_func

logger = logging.getLogger(__name__)


def enqueue_clone_job(
    payload: CloneRequest,
    redis_conn: redis.Redis,
    rq_queue: Queue,
) -> CloneResponse:
    """Validates request, enqueues the job, and sets initial status in Redis."""
    try:
        pass  # Validation is handled by Pydantic model binding in FastAPI
    except ValidationError as e:
        logger.warning(f"Invalid URL received: {payload.url}. Error: {e}")
        raise HTTPException(status_code=422, detail=f"Invalid URL: {e.errors()}")

    job_id = uuid.uuid4().hex
    try:
        func_args = (job_id, str(payload.url), payload.capture_full_page)
        rq_job = rq_queue.enqueue(
            run_clone_orchestrator_func,
            args=func_args,
            job_id=job_id,
            description=f"Cloning job for {payload.url}",
            job_timeout=3600,
        )
        logger.info(
            f"Enqueued job {job_id} (RQ ID: {rq_job.id}) for URL: {payload.url}"
        )

        initial_status_data = {
            "job_id": job_id,
            "state": JobStatus.PENDING.value,
            "message": "Job received and queued.",
            "original_url": str(payload.url),
            "capture_full_page_setting": str(payload.capture_full_page),
            "timestamp": datetime.datetime.utcnow().isoformat(),
            "rq_job_id": rq_job.id,
        }
        status_to_set = {k: str(v) for k, v in initial_status_data.items()}
        redis_conn.hset(f"job:{job_id}", mapping=status_to_set)
        logger.info(f"Initialized status for job {job_id} in Redis.")

    except redis.exceptions.RedisError as e:
        logger.error(f"Redis error during job enqueue or status init for {job_id}: {e}")
        raise HTTPException(
            status_code=503, detail="Service temporarily unavailable (Redis error)."
        )
    except Exception as e:
        logger.error(f"Unexpected error during job enqueue for {job_id}: {e}")
        raise HTTPException(
            status_code=500, detail="Internal server error during job submission."
        )

    return CloneResponse(job_id=job_id)


def get_job_status(job_id: str, redis_conn: redis.Redis) -> StatusResponse:
    """Retrieves and formats the job status from Redis."""
    job_key = f"job:{job_id}"
    try:
        status_data_bytes = redis_conn.hgetall(job_key)
        if not status_data_bytes:
            logger.warning(f"Job status requested for non-existent job_id: {job_id}")
            raise HTTPException(
                status_code=404, detail=f"Job with ID '{job_id}' not found."
            )

        status_data = {
            k.decode("utf-8"): v.decode("utf-8") for k, v in status_data_bytes.items()
        }

        # Clean up empty URL fields to be None for Pydantic
        url_fields_to_check = [
            "artifact_url",
            "screenshot_url",
            "cloned_screenshot_url",
            "diff_heatmap_url",
        ]
        for field in url_fields_to_check:
            if field in status_data and status_data[field] == "":
                status_data[field] = None

        # Safely convert numeric fields
        if "ssim" in status_data and status_data["ssim"]:
            try:
                status_data["ssim"] = float(status_data["ssim"])
            except (ValueError, TypeError):
                logger.warning(
                    f"Could not convert ssim '{status_data['ssim']}' to float for job {job_id}"
                )
                status_data["ssim"] = None
        if "attempts" in status_data and status_data["attempts"]:
            try:
                status_data["attempts"] = int(status_data["attempts"])
            except (ValueError, TypeError):
                logger.warning(
                    f"Could not convert attempts '{status_data['attempts']}' to int for job {job_id}"
                )
                status_data["attempts"] = None

        if "job_id" not in status_data:
            status_data["job_id"] = job_id
        if "state" not in status_data:
            logger.error(
                f"State missing for job {job_id} in Redis. Defaulting to error."
            )
            status_data["state"] = JobStatus.ERROR.value
            status_data["message"] = "Job state inconsistent in storage."

        return StatusResponse(**status_data)

    except redis.exceptions.RedisError as e:
        logger.error(f"Redis error while fetching status for job {job_id}: {e}")
        raise HTTPException(
            status_code=503, detail="Service temporarily unavailable (Redis error)."
        )
    except ValidationError as e:
        logger.error(
            f"Data validation error for job status {job_id}: {status_data}. Error: {e}"
        )
        return StatusResponse(
            job_id=job_id,
            state=JobStatus.ERROR,
            message=f"Error retrieving job status: data format issue. Details: {e.errors()}",
        )
    except Exception as e:
        logger.error(f"Unexpected error fetching status for job {job_id}: {e}")
        raise HTTPException(
            status_code=500, detail="Internal server error retrieving job status."
        )
