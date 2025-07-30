"""
TraceLab SDK for Python applications.

This SDK automatically traces interactions with external services
and sends trace events to the TraceLab backend for visualization.
"""

import json
import os
import uuid
from functools import wraps
from typing import Callable, Dict, Optional, Any

import redis

from . import state
from .patching import patch_all

__all__ = ["init", "trace", "register_hook", "shutdown"]


def init(
    workflow_name: str,
    service_name: Optional[str] = None,
    redis_url: Optional[str] = None,
    run_id: Optional[str] = None,
    tags: Optional[Dict[str, Any]] = None,
) -> None:
    """
    Initialize the TraceLab SDK.

    Args:
        workflow_name: Name of the workflow being traced
        service_name: Name of the service (defaults to hostname)
        redis_url: Redis connection URL
        run_id: Unique execution ID (auto-generated if not provided)
        tags: Additional metadata tags for the trace
    """
    if not workflow_name:
        raise ValueError("workflow_name is required")

    # Set workflow configuration
    state.workflow_name = workflow_name
    state.service_name = service_name or os.environ.get(
        "TRACELAB_SERVICE_NAME", os.uname().nodename
    )
    state.run_id = run_id or os.environ.get("TRACELAB_RUN_ID", str(uuid.uuid4()))
    state.tags = tags or {}

    # Initialize Redis connection
    redis_url = redis_url or os.environ.get(
        "TRACELAB_REDIS_URL", "redis://redis:6379/0"
    )
    state.redis_client = redis.from_url(redis_url)

    # Apply automatic patching
    patch_all()

    # Send initialization event
    _send_trace_event({"event_type": "INIT", "status": "STARTED"})


def shutdown() -> None:
    """
    Shutdown the TraceLab SDK and send completion event.
    """
    if state.redis_client is None:
        return

    _send_trace_event({"event_type": "SHUTDOWN", "status": "COMPLETED"})

    state.redis_client.close()
    state.redis_client = None


def trace(name: Optional[str] = None, service: Optional[str] = None) -> Callable:
    """
    Decorator to trace function execution.

    Args:
        name: Custom name for the traced operation
        service: Service name override for this trace

    Returns:
        Decorated function
    """

    def decorator(func: Callable) -> Callable:
        operation_name = name or func.__name__

        @wraps(func)
        def wrapper(*args, **kwargs):
            if state.redis_client is None:
                return func(*args, **kwargs)

            trace_event = {
                "service_name": service or state.service_name,
                "endpoint": operation_name,
                "request": {"args": str(args), "kwargs": str(kwargs)},
            }

            try:
                result = func(*args, **kwargs)
                trace_event["response"] = {"result": str(result)}
                return result
            except Exception as e:
                trace_event["response"] = {
                    "error": str(e),
                    "error_type": type(e).__name__,
                }
                raise
            finally:
                _send_trace_event(trace_event)

        return wrapper

    return decorator


def register_hook(
    library_name: str, function_name: str, hook_function: Callable
) -> None:
    """
    Register a custom hook for tracing library interactions.

    Args:
        library_name: Name of the library to hook
        function_name: Name of the function to intercept
        hook_function: Function to capture trace data
    """
    if library_name not in state.hooks:
        state.hooks[library_name] = {}

    state.hooks[library_name][function_name] = hook_function


def _send_trace_event(event_data: Dict[str, Any]) -> None:
    """
    Send a trace event to Redis.

    Args:
        event_data: Event data to send
    """
    if state.redis_client is None:
        return

    # Add common fields
    trace_event = {
        "workflow_name": state.workflow_name,
        "service_name": state.service_name,
        "run_id": state.run_id,
        "tags": state.tags,
        **event_data,
    }

    try:
        state.redis_client.xadd("trace.events", {"data": json.dumps(trace_event)})
    except Exception as e:
        # Log error but don't crash the application
        print(f"TraceLab SDK error sending event: {e}")
