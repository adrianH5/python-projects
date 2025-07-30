import datetime
import logging
from typing import Dict, Any

import numpy as np
import redis

from app.core.config import settings

logger = logging.getLogger(__name__)


def update_job_status(job_id: str, status_update: Dict[str, Any]):
    """
    Updates a job's status in Redis.

    Connects to Redis, formats values, and uses HSET to update the job hash.
    It adds a timestamp to each update.

    Args:
        job_id: The ID of the job to update.
        status_update: A dictionary of fields and values to update.
    """
    try:
        update_for_redis = {}
        for k, v in status_update.items():
            if v is None:
                update_for_redis[k] = ""
            elif isinstance(v, (float, np.float32, np.float64)):
                update_for_redis[k] = f"{v:.4f}"
            elif isinstance(v, bool):
                update_for_redis[k] = str(v).lower()
            else:
                update_for_redis[k] = str(v)

        redis_conn = redis.Redis.from_url(settings.REDIS_URL, decode_responses=False)
        job_key = f"job:{job_id}"
        update_for_redis["timestamp"] = datetime.datetime.utcnow().isoformat()
        if "job_id" not in update_for_redis:
            update_for_redis["job_id"] = job_id

        byte_update = {
            k.encode("utf-8"): str(v).encode("utf-8")
            for k, v in update_for_redis.items()
        }
        redis_conn.hset(job_key.encode("utf-8"), mapping=byte_update)

        log_context_job_id = update_for_redis.get("job_id", job_id)
        logger.info(
            f"Job {log_context_job_id}: Status fields updated in Redis: {update_for_redis}"
        )
        redis_conn.close()
    except redis.exceptions.RedisError as e:
        logger.error(
            f"Job {job_id}: Redis error updating status: {e}. Update was: {update_for_redis}"
        )
    except Exception as e:
        logger.error(
            f"Job {job_id}: Unexpected error updating status in Redis: {e}. Update was: {status_update}",
            exc_info=True,
        )
