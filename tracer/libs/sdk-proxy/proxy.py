import hashlib
import json
import os
import time

import redis
from mitmproxy import http

REDIS_URL = os.environ.get("REDIS_URL", "redis://localhost:6379/0")
WORKFLOW_NAME = os.environ.get("TRACELAB_WORKFLOW_NAME")
SERVICE_NAME = os.environ.get("TRACELAB_SERVICE_NAME")
TRACELAB_RUN_ID = os.environ.get("TRACELAB_RUN_ID")
TRACE_EVENTS_STREAM = "trace.events"

if not WORKFLOW_NAME:
    raise ValueError("TRACELAB_WORKFLOW_NAME environment variable must be set")
if not SERVICE_NAME:
    raise ValueError("TRACELAB_SERVICE_NAME environment variable must be set")


try:
    redis_client = redis.from_url(REDIS_URL)
    redis_client.ping()
    print(f"SDK-PROXY: Connected to Redis at {REDIS_URL}", flush=True)
except redis.exceptions.ConnectionError as e:
    print(f"SDK-PROXY: Could not connect to Redis: {e}", flush=True)
    redis_client = None


def hash_content(content: bytes | None) -> str | None:
    """Hashes content using SHA256 if it exists, otherwise returns None."""
    if content:
        return hashlib.sha256(content).hexdigest()
    return None


def response(flow: http.HTTPFlow) -> None:
    """
    This function is called for each HTTP response.
    It captures request/response data, hashes it, and publishes a trace event to Redis.
    """
    if not redis_client:
        print(
            "SDK-PROXY: Redis client not available. Skipping trace event.", flush=True
        )
        return

    # We are only interested in responses from servers
    if not flow.response:
        return

    latency_ms = None
    if flow.request.timestamp_start and flow.response.timestamp_end:
        latency_ms = int(
            (flow.response.timestamp_end - flow.request.timestamp_start) * 1000
        )

    request_body_hash = hash_content(flow.request.content)
    response_body_hash = hash_content(flow.response.content)

    trace_event = {
        "workflow_name": WORKFLOW_NAME,
        "service_name": SERVICE_NAME,
        "event_type": "http_request_response",
        "timestamp": time.time(),
        "latency_ms": latency_ms,
        "request": {
            "url": flow.request.pretty_url,
            "method": flow.request.method,
            "headers": dict(flow.request.headers),
            "body_hash": request_body_hash,
        },
        "response": {
            "status_code": flow.response.status_code,
            "headers": dict(flow.response.headers),
            "body_hash": response_body_hash,
        },
    }

    if TRACELAB_RUN_ID:
        trace_event["run_id"] = TRACELAB_RUN_ID

    try:
        event_data = json.dumps(trace_event)
        redis_client.xadd(TRACE_EVENTS_STREAM, {"data": event_data})
        print(
            f"SDK-PROXY: Published trace event for {flow.request.method} {flow.request.pretty_url}",
            flush=True,
        )
    except redis.exceptions.RedisError as e:
        print(f"SDK-PROXY: Failed to publish trace event to Redis: {e}", flush=True)
