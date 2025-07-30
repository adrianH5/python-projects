"""
TraceLab API main application module.

This module initializes the FastAPI application with middleware,
routers, and background tasks for trace event recording.
"""

import asyncio
from typing import Optional

from fastapi import FastAPI
from fastapi.middleware.cors import CORSMiddleware
from starlette_prometheus import PrometheusMiddleware, metrics

from api.app.background.recorder import recorder_worker
from api.app.core.config import settings
from api.app.db.init_db import init_db
from api.app.db.session import SessionLocal
from api.app.v1.router import api_router
from api.app.websocket import websocket_router


class AppState:
    """Application state container for managing background tasks."""

    def __init__(self):
        self.recorder_task: Optional[asyncio.Task] = None


app_state = AppState()


def create_application() -> FastAPI:
    """
    Create and configure the FastAPI application instance.

    Returns:
        FastAPI: Configured application instance
    """
    application = FastAPI(
        title=settings.PROJECT_NAME, openapi_url=f"{settings.API_V1_STR}/openapi.json"
    )

    configure_middleware(application)
    configure_routes(application)
    configure_event_handlers(application)

    return application


def configure_middleware(application: FastAPI) -> None:
    """
    Configure application middleware for CORS and monitoring.

    Args:
        application: FastAPI application instance
    """
    cors_origins = ["http://localhost:3000"]

    application.add_middleware(
        CORSMiddleware,
        allow_origins=cors_origins,
        allow_credentials=True,
        allow_methods=["*"],
        allow_headers=["*"],
    )
    application.add_middleware(PrometheusMiddleware)
    application.add_route("/metrics", metrics)


def configure_routes(application: FastAPI) -> None:
    """
    Configure application routes and API routers.

    Args:
        application: FastAPI application instance
    """
    application.include_router(api_router, prefix=settings.API_V1_STR)
    application.include_router(websocket_router)


def configure_event_handlers(application: FastAPI) -> None:
    """
    Configure application startup and shutdown event handlers.

    Args:
        application: FastAPI application instance
    """
    application.add_event_handler("startup", startup_event)
    application.add_event_handler("shutdown", shutdown_event)


async def startup_event() -> None:
    """Initialize database and start background recorder worker."""
    initialize_database()
    await start_recorder_worker()


async def shutdown_event() -> None:
    """Gracefully shutdown background recorder worker."""
    await stop_recorder_worker()


def initialize_database() -> None:
    """Initialize database schema and required data."""
    db = SessionLocal()
    try:
        init_db(db)
    finally:
        db.close()


async def start_recorder_worker() -> None:
    """Start the background recorder worker task."""
    app_state.recorder_task = asyncio.create_task(recorder_worker())


async def stop_recorder_worker() -> None:
    """Stop the background recorder worker task gracefully."""
    if app_state.recorder_task is None:
        return

    app_state.recorder_task.cancel()

    try:
        await app_state.recorder_task
    except asyncio.CancelledError:
        pass


app = create_application()


@app.get("/")
def read_root():
    """Root endpoint returning welcome message."""
    return {"message": "Welcome to TraceLab API"}
