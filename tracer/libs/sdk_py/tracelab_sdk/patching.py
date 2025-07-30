import wrapt
import requests
import time
import json
from . import state


def _capture_request(wrapped, instance, args, kwargs):
    start_time = time.time()
    response = None
    error = None

    try:
        response = wrapped(*args, **kwargs)
        response.raise_for_status()
    except requests.exceptions.RequestException as e:
        response = e.response
        error = str(e)

    latency_ms = int((time.time() - start_time) * 1000)

    if state._redis_client:
        # Extract body safely
        req_body = kwargs.get("json") or kwargs.get("data")

        # Attempt to get response body
        try:
            res_body = (
                response.json()
                if response
                and response.headers.get("Content-Type") == "application/json"
                else (response.text if response else None)
            )
        except json.JSONDecodeError:
            res_body = response.text if response else None

        state._step_index += 1
        trace_event = {
            "workflow_name": state._workflow_name,
            "service_name": state._service_name,
            "idx": state._step_index,
            "service": "http",
            "endpoint": f"{response.request.method} {response.request.url}",
            "request": {
                "method": response.request.method,
                "url": response.request.url,
                "headers": dict(response.request.headers),
                "body": req_body,
            },
            "response": {
                "status_code": response.status_code if response else None,
                "headers": dict(response.headers) if response else None,
                "body": res_body,
            },
            "latency_ms": latency_ms,
            "error": error,
        }
        state._redis_client.xadd(
            "trace.events", {"data": json.dumps(trace_event, default=str)}
        )
        print(f"Trace event sent to Redis: {trace_event['endpoint']}")

    if error:
        raise requests.exceptions.RequestException(error, response=response)

    return response


def patch_all():
    wrapt.wrap_function_wrapper("requests", "api.request", _capture_request)
    wrapt.wrap_function_wrapper("requests", "request", _capture_request)
    wrapt.wrap_function_wrapper("requests", "get", _capture_request)
    wrapt.wrap_function_wrapper("requests", "post", _capture_request)
