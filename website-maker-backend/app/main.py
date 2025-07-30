import logging
from contextlib import asynccontextmanager
from fastapi import FastAPI
from fastapi.middleware.cors import CORSMiddleware
import redis
from rq import Queue

from app.core.config import settings
from app.api.router import router as api_router
from app.services.storage import ensure_bucket_exists  # To ensure bucket on startup

# Configure logging
logging.basicConfig(level=logging.INFO)
logger = logging.getLogger(__name__)


@asynccontextmanager
async def lifespan(app: FastAPI):
    """
    Application lifespan manager.
    - On startup: Initialize Redis connection, RQ queue, and ensure MinIO bucket exists.
    - On shutdown: Close Redis connection.
    """
    logger.info("Application startup...")

    # Initialize Redis connection
    try:
        app.state.redis_conn = redis.Redis.from_url(settings.REDIS_URL)
        app.state.redis_conn.ping()
        logger.info("Successfully connected to Redis.")
    except redis.exceptions.ConnectionError as e:
        logger.error(f"Failed to connect to Redis: {e}")
        # we'll log and continue, but operations requiring Redis will fail.
        app.state.redis_conn = None

    # Initialize RQ queue
    if app.state.redis_conn:
        app.state.rq_queue = Queue(
            settings.CLONE_QUEUE_NAME, connection=app.state.redis_conn
        )
        logger.info(f"RQ queue '{settings.CLONE_QUEUE_NAME}' initialized.")
    else:
        app.state.rq_queue = None
        logger.warning(
            f"RQ queue '{settings.CLONE_QUEUE_NAME}' could not be initialized due to Redis connection failure."
        )

    # Ensure MinIO bucket exists
    logger.info(f"Ensuring MinIO bucket '{settings.MINIO_BUCKET_NAME}' exists...")
    if not ensure_bucket_exists(settings.MINIO_BUCKET_NAME):
        logger.warning(
            f"Failed to ensure MinIO bucket '{settings.MINIO_BUCKET_NAME}' exists or is accessible. "
            "File operations may fail."
        )
    else:
        logger.info(f"MinIO bucket '{settings.MINIO_BUCKET_NAME}' is ready.")

    logger.info("Application startup complete.")

    yield

    # Shutdown logic
    logger.info("Application shutdown...")
    if hasattr(app.state, "redis_conn") and app.state.redis_conn:
        app.state.redis_conn.close()
        logger.info("Redis connection closed.")
    logger.info("Application shutdown complete.")


# Init
app = FastAPI(
    title="Website-Cloner API",
    description="API for cloning websites, managing jobs, and serving artifacts.",
    version="0.1.0",
    lifespan=lifespan,
)

# CORS
origins = [
    "http://localhost:3000",  # Next.js frontend
    "http://127.0.0.1:3000",  # Also for Next.js
]

app.add_middleware(
    CORSMiddleware,
    allow_origins=origins,
    allow_credentials=True,
    allow_methods=["*"],  # Allows all methods (GET, POST, etc.)
    allow_headers=["*"],  # Allows all headers
)


# the API router
app.include_router(api_router, prefix="/api")  # All API routes will be under /api


# Root endpoint for health check or basic info
@app.get("/", summary="Health Check", tags=["General"])
async def read_root():
    """
    Root endpoint providing a basic health check / welcome message.
    """
    return {"message": "Welcome to the  Website-Cloner API!"}


# from fastapi import Depends
# def get_redis(request: Request):
#     return request.app.state.redis_conn
#
# def get_rq_queue(request: Request):
#     return request.app.state.rq_queue

if __name__ == "__main__":
    import uvicorn

    # This is for local development if not using `docker compose up`
    # `docker compose up` uses the command specified in docker-compose.yml
    logger.info("Starting Uvicorn server for local development...")
    uvicorn.run(app, host="0.0.0.0", port=8000, log_level="info")
