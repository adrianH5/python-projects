import logging
import sys
import datetime

import redis
from rq import Worker

from app.core.config import settings
from app.schemas.job import JobStatus

# Configure logging for the worker
# Ensure logs go to stdout for Docker container logging
logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s - %(name)s - %(levelname)s - %(message)s",
    stream=sys.stdout,
)
logger = logging.getLogger(__name__)


def update_job_status_on_worker_failure(job, exc_type, exc_value, tb_obj):
    """
    Custom RQ exception handler.
    This function is called by RQ when a job execution raises an unhandled exception.
    It updates the job's status in our Redis hash to 'error' and logs the exception.

    Args:
        job (rq.Job): The job instance that failed.
        exc_type (Type[BaseException]): The type of the exception.
        exc_value (BaseException): The exception instance.
        tb_obj (traceback): The traceback object.

    Returns:
        bool: False to allow other exception handlers (like RQ's default) to run.
              True would stop further handlers.
    """
    # job.args should contain (job_id, url_str) as passed from api.py
    job_id_custom = None
    if job.args and len(job.args) > 0:
        job_id_custom = job.args[0]  # job_id is the first argument
    # No fallback to kwargs needed here as api.py now exclusively uses args for function parameters

    # Log the failure with as much detail as possible
    full_traceback_str = "".join(tb_obj.format())
    if job_id_custom:
        logger.error(
            f"Job {job_id_custom} (RQ ID: {job.id}) failed with {exc_type.__name__}: {exc_value}."
        )
        logger.error(f"Traceback for job {job_id_custom}:\n{full_traceback_str}")
    else:
        # This case should ideally not happen if jobs are enqueued correctly
        logger.error(
            f"RQ Job {job.id} failed, but custom 'job_id' not found in job.kwargs. "
            f"Cannot update detailed status in 'job:{{job_id}}' hash. Exception: {exc_value}"
        )
        logger.error(f"Traceback for RQ Job {job.id}:\n{full_traceback_str}")
        # Still allow RQ's default handling
        return False

    # Update the job status in our specific Redis hash
    try:
        # Create a new Redis connection for this handler to ensure atomicity/isolation
        # The worker's main connection might be busy or in an uncertain state.
        redis_conn = redis.Redis.from_url(settings.REDIS_URL, decode_responses=True)
        job_key = f"job:{job_id_custom}"

        # Prepare update data
        # The orchestrator.run_clone task itself should also try to set state to ERROR on failure.
        # This handler is a fallback for unhandled exceptions bubbling up from the task.
        current_status = redis_conn.hgetall(job_key)
        if (
            current_status.get("state") != JobStatus.ERROR.value
        ):  # Avoid overwriting a more specific error from task
            update_data = {
                "state": JobStatus.ERROR.value,
                "message": f"Worker error: {exc_type.__name__}: {str(exc_value)}",  # Concise error
                "timestamp": datetime.datetime.utcnow().isoformat(),
                # "detailed_error": full_traceback_str[:2000] # Optional: store part of traceback
            }
            # Use hset for multiple fields (hmset is deprecated)
            # Ensure values are appropriate for hset (typically strings)
            update_to_set = {k: str(v) for k, v in update_data.items()}
            redis_conn.hset(job_key, mapping=update_to_set)
            logger.info(
                f"Updated status for failed job {job_id_custom} to ERROR in Redis due to worker exception."
            )
        else:
            logger.info(
                f"Job {job_id_custom} status already ERROR. Worker handler skipping update."
            )
        redis_conn.close()
    except redis.exceptions.RedisError as e_redis:
        logger.error(
            f"Redis error while updating status for failed job {job_id_custom} in worker handler: {e_redis}"
        )
    except Exception as e_update:
        logger.error(
            f"Unexpected error updating status for failed job {job_id_custom} in worker handler: {e_update}"
        )

    # Return False to allow RQ's default exception handler to run.
    # RQ's default handler (typically default_failure_handler) logs the exception
    # and moves the job to the FailedJobRegistry (formerly FailedQueue).
    return False


if __name__ == "__main__":
    logger.info("Initializing RQ Worker process...")
    logger.info(f"Attempting to connect to Redis at: {settings.REDIS_URL}")
    logger.info(f"Will listen on queue: {settings.CLONE_QUEUE_NAME}")

    # The Python module path should be set up correctly for 'app.orchestrator.run_clone' to be found.
    # When running `python -m app.worker` from the `/code` directory (where `app` is a subdirectory),
    # Python automatically adds `/code` to sys.path, so `app.orchestrator` can be imported.

    redis_connection_instance = None  # Define in outer scope for finally block
    try:
        # Establish Redis connection
        redis_connection_instance = redis.Redis.from_url(settings.REDIS_URL)
        redis_connection_instance.ping()  # Verify connection
        logger.info(
            f"Successfully connected to Redis for RQ Worker at {settings.REDIS_URL}"
        )

        queues_to_listen = [settings.CLONE_QUEUE_NAME]

        # Create the worker instance, passing the connection directly.
        worker_instance = Worker(
            queues=queues_to_listen,
            connection=redis_connection_instance,  # Pass the connection here
            exception_handlers=[update_job_status_on_worker_failure],
            # name= can be used to give a custom name to the worker instance.
            # default_timeout= can set a default timeout for jobs processed by this worker.
        )
        logger.info(f"RQ Worker '{worker_instance.name}' initialized successfully.")
        logger.info(f"Starting worker, listening on queues: {queues_to_listen}...")
        # worker_instance.work() is a blocking call.
        # burst=False (default) means it runs indefinitely, listening for new jobs.
        # with_scheduler=False (default) means it doesn't run RQ-Scheduler tasks.
        worker_instance.work(
            logging_level="INFO"
        )  # Use RQ's internal logging at INFO level.

    except redis.exceptions.ConnectionError as e:
        logger.error(
            f"Could not connect to Redis: {e}. RQ Worker cannot start.", exc_info=True
        )
        sys.exit(1)  # Exit if Redis connection fails on startup
    except KeyboardInterrupt:
        logger.info("RQ Worker shutting down due to KeyboardInterrupt...")
        # Worker should attempt graceful shutdown of current job if possible.
    except Exception as e:
        logger.error(f"RQ Worker crashed unexpectedly: {e}", exc_info=True)
        sys.exit(1)  # Exit with error code if worker has an unrecoverable crash
    finally:
        if redis_connection_instance:  # Check if it was successfully created
            try:
                redis_connection_instance.close()
                logger.info("Worker's Redis connection closed.")
            except Exception as e_close:
                logger.error(f"Error closing worker's Redis connection: {e_close}")
        logger.info("RQ Worker process has stopped.")
