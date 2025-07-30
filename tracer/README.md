# TraceLab

TraceLab lets developers record and debug agent interactions with external services. (THIS IS A VERY BAREBONES TOOL, as it was more of a learning project)

## Key Features

- **Record & Trace:** Automatically capture all external interactions (HTTP, gRPC, email, etc.) made by your AI agents.
- **Timeline Debugging:** Visualize the entire execution flow on a real-time UI, inspect payloads and responses, and identify the root cause of failures.
- **Extensible SDKs:** Use the Python and TypeScript SDKs to easily integrate TraceLab into your existing applications. Add custom hooks to trace any protocol or library.
- **Zero-Code Tracing:** Capture traffic from any application, including closed-source binaries, using the built-in MITM proxy.
- **Full Observability:** Get deep insights into your system's performance with built-in OpenTelemetry, Prometheus, and Grafana integration.

## End-to-End Workflow

Here's a detailed breakdown of the typical TraceLab workflow for logging and visualizing agent interactions.

**1. Instrument Your Application**

The first step is to add the TraceLab SDK to your application.

- **Install the SDK:** The TraceLab SDKs are not published to public package registries. You must install them from their local paths within this mono-repo. See the [SDK Installation](#sdk-installation) section for detailed instructions.
- **Initialize the SDK:** Call the `init()` function at the beginning of your application's entry point. This will automatically patch popular libraries to capture their interactions.

**2. Record an Execution**

Once the SDK is installed and initialized, simply run your application as you normally would.

- **Run your code:** As your application runs, the SDK captures every interaction with the patched libraries (e.g., every `requests.post()` call).
- **Publish TraceEvents:** For each interaction, the SDK creates a `TraceEvent` and publishes it to a Redis stream. A `TraceEvent` is a JSON object containing the service name, endpoint, request and response data, latency, and other metadata.
- **Group into Executions:** The TraceLab API consumes the `TraceEvent` stream from Redis and groups related events into an `Execution`. An `Execution` represents a single, end-to-end run of your workflow.

**3. View the Timeline**

Navigate to the TraceLab frontend in your browser ([http://localhost:3000](http://localhost:3000)) to view the recorded executions.

- **Workflow List:** The main page lists all the recorded workflows.
- **Execution Timeline:** Clicking on a workflow will take you to a list of its executions. Selecting an execution will display a detailed timeline view (a Gantt chart) of all the steps in that execution.
- **Inspect Payloads:** You can click on any step in the timeline to inspect the full request and response payloads, headers, and other metadata.

## SDK Installation

The TraceLab SDKs are local packages and must be installed from their respective directories within this mono-repo.

### Python SDK

To install the Python SDK, run the following command from the root of the `tracelab` directory:

```bash
pip install libs/sdk_py
```

### TypeScript SDK

To install the TypeScript SDK, run the following command from the root of the `tracelab` directory:

```bash
npm install ./libs/sdk_ts
```

This will install the SDK as a local dependency in your project's `node_modules` directory.

1.  **Clone the repository:**

    ```bash
    git clone <repository-url>
    cd tracelab
    ```

2.  **Start the development environment:**

    ```bash
    make dev
    ```

    This will build the Docker images and start all services using Docker Compose.

3.  **Access the applications:**
    - **Frontend:** [http://localhost:3000](http://localhost:3000)
    - **API (Swagger UI):** [http://localhost:8000/docs](http://localhost:8000/docs)
    - **Grafana:** [http://localhost:4000](http://localhost:4000)

## Running the Sample Test Application

This repository includes a sample test application in the `tracer-test` directory that demonstrates how to use the Python SDK to trace interactions with the mock services.

To run the sample test:

1.  **Install the Python SDK:**

    ```bash
    pip install ./libs/sdk_py
    ```

2.  **Ensure the TraceLab environment is running:**

    ```bash
    make dev
    ```

3.  **Run the test script:**
    ```bash
    python tracer-test/test_app.py
    ```

After running the script, you can navigate to the TraceLab UI at [http://localhost:3000](http://localhost:3000) to view the "sample-test-run" workflow and inspect the captured traces.

## Using the SDK

To trace your application, you can use the Python or TypeScript SDK.

**Important:** The TraceLab Docker environment must be running (`make dev`) for the SDK to capture and send traces to the backend services. The SDK connects to the Redis instance within the Docker network to publish trace events.

### Python

**Usage**

The Python SDK automatically patches the following libraries:

- `requests`
- `httpx`
- `smtplib`
- `boto3` (specifically the SES client)
- `twilio`

```python
from tracelab_sdk import init, trace
import requests

# Initialize the SDK
init(
    workflow_name="my-awesome-workflow",
    service_name="my-python-service",
)

# This request will be automatically traced
requests.get("https://www.google.com")

# You can also use the @trace decorator for custom functions
@trace
def my_custom_function():
    # ... your code here ...
    pass

my_custom_function()
```

### TypeScript

**Usage**

The TypeScript SDK automatically patches the following:

- `fetch` (global)
- `@sendgrid/mail`

```typescript
import { init, trace } from "@tracelab/sdk";
import fetch from "node-fetch";

// Initialize the SDK
init({
  workflowName: "my-awesome-workflow",
  serviceName: "my-typescript-service",
});

// This request will be automatically traced
fetch("https://www.google.com");

// You can also use the trace function for custom code blocks
trace("my-custom-function", async () => {
  // ... your code here ...
});
```

## Environment Variables

| Variable                 | Default                                   | Purpose                                 |
| ------------------------ | ----------------------------------------- | --------------------------------------- |
| `TRACELAB_REDIS_URL`     | `redis://redis:6379/0`                    | Where SDK publishes `TraceEvent` JSON   |
| `TRACELAB_WORKFLOW_NAME` | _(required)_                              | Logical group for this run              |
| `TRACELAB_SERVICE_NAME`  | `hostname`                                | Per-lane label in timeline              |
| `TRACELAB_RUN_ID`        | `uuid.uuid4()`                            | Unique ID for a single execution        |
| `HTTP(S)_PROXY`          | _(unset)_                                 | MITM proxy URL to auto-record raw HTTP  |
| `TRACELAB_TAGS`          | `{}`                                      | Free-form JSON string for search/filter |
| `DATABASE_URL`           | `postgresql://trace:trace@postgres/trace` | Database connection string for the API  |
| `REDIS_URL`              | `redis://redis:6379/0`                    | Redis connection string for the API     |

## Extending TraceLab

TraceLab is designed to be extensible. Here are the primary ways you can adapt it to your needs:

### 1. Adding a New Mock Service

They are lightweight web servers that simulate the behavior of real-world vendor APIs.

**How They Work**

When you run a replay, TraceLab's ReplayEngine spins up an ephemeral Docker network containing your application and the necessary mock services. The ReplayEngine then intercepts the network calls your application makes and redirects them to the appropriate mock service instead of the actual vendor API.

This approach provides several key benefits:

- **Isolation:** Replays run in a completely isolated environment, so you don't have to worry about making real API calls, sending accidental emails, or incurring costs.
- **Determinism:** Mock services can be configured to return predictable responses, ensuring that your replays are deterministic and repeatable.
- **Speed:** Since there are no real network calls involved, replays are significantly faster than running your application against live APIs.
- **Chaos Testing:** You can introduce failures and latency into the mock services to test how your application handles various error conditions.

To add a new mock service for a vendor API (e.g., Stripe), follow these steps:

**a. Create the Mock Service Directory**

Create a new directory at the root of the project for your mock service, for example, `mock-stripe`.

**b. Implement the Mock API**

Inside `mock-stripe`, create a simple web server that mimics the Stripe API endpoints your application uses. You can use any framework you like, but Flask is a good choice for simple mocks.

**`mock-stripe/app.py`:**

```python
from flask import Flask, jsonify, request

app = Flask(__name__)

@app.route('/v1/charges', methods=['POST'])
def create_charge():
    # You can add logic here to simulate different responses
    # based on the request payload or environment variables.
    return jsonify({
        "id": "ch_123456789",
        "amount": request.json.get("amount", 1000),
        "status": "succeeded"
    })

if __name__ == '__main__':
    app.run(host='0.0.0.0', port=5000)
```

**c. Create a Dockerfile**

Add a `Dockerfile` to build your mock service image.

**`mock-stripe/Dockerfile`:**

```dockerfile
FROM python:3.12-slim
WORKDIR /app
RUN pip install flask
COPY app.py /app/
CMD ["flask", "run", "--host=0.0.0.0"]
```

**d. Add the Service to Docker Compose**

Finally, add your new mock service to the `docker-compose.yml` file.

```yaml
# docker-compose.yml

services:
  # ... other services
  mock-stripe:
    build:
      context: ./mock-stripe
```

Now, when you run `make dev`, your `mock-stripe` service will be available to your application within the Docker network.

### 2. Adding a New SDK Hook

The SDKs use hooks to intercept and record interactions with various libraries. If you're using a library that isn't supported out-of-the-box, you can add your own hook.

**How They Work**

The process works as follows:

1.  **Registration:** You use the `register_hook` function provided by the SDK to specify the target library and function you want to trace, along with the hook function that will be used to capture the interaction.
2.  **Interception:** The SDK uses monkey-patching to replace the target function with a wrapper.
3.  **Execution & Capture:** When your application calls the target function, the wrapper executes your hook function, passing the original function's arguments. Your hook then captures the relevant information and returns a structured dictionary (a `TraceEvent`).
4.  **Publishing:** The SDK sends the `TraceEvent` to the TraceLab backend, where it is recorded and displayed on the timeline.

This mechanism allows you to trace anything from database queries and gRPC calls to interactions with custom hardware.

**Python SDK Hook**

To add a hook to the Python SDK, use the `register_hook` function. The hook function receives the arguments of the original function and should return a dictionary with the details of the interaction.

Here's an example of a hook for a hypothetical `my_database_library`:

```python
from tracelab_sdk import init, register_hook
import my_database_library

def capture_db_query(query, params):
    return {
        "service": "database",
        "endpoint": "query",
        "request": {"query": query, "params": params},
        "response": {"status": "success"}, # Or capture the actual result
    }

register_hook(my_database_library, "execute", capture_db_query)

init(workflow_name="db-workflow", service_name="db-service")

my_database_library.execute("SELECT * FROM users", [1, 2, 3])
```

**TypeScript SDK Hook**

The process is similar for the TypeScript SDK. You would use the `registerHook` function to wrap the target function.

```typescript
import { init, registerHook } from "@tracelab/sdk";
import { myDatabaseLibrary } from "./my-db-lib";

function captureDbQuery(query: string, params: any[]) {
  return {
    service: "database",
    endpoint: "query",
    request: { query, params },
    response: { status: "success" },
  };
}

registerHook(myDatabaseLibrary, "execute", captureDbQuery);

init({
  workflowName: "db-workflow",
  serviceName: "db-service",
});

myDatabaseLibrary.execute("SELECT * FROM users", [1, 2, 3]);
```

### 3. Zero-Code Capture with the MITM Proxy

For applications where you cannot modify the code (e.g., closed-source binaries or third-party tools), you can use the built-in MITM (Man-in-the-Middle) proxy to capture all outgoing HTTP and HTTPS traffic.

In the context of TraceLab, the `sdk-proxy` service acts as a MITM proxy. When you configure your application to use it, all outgoing HTTP and HTTPS requests are routed through the proxy.

**How it Works**

1.  **Configuration:** You set the `HTTP_PROXY` and `HTTPS_PROXY` environment variables in your application's environment. Most applications and command-line tools automatically recognize and use these variables to route their traffic through the specified proxy.
2.  **Interception:** The `sdk-proxy` service, which is powered by `mitmproxy`, intercepts the requests. For HTTPS traffic, it generates a temporary, self-signed SSL certificate on the fly, allowing it to decrypt, inspect, and re-encrypt the traffic without the client or server knowing.
3.  **Recording:** The proxy records the details of each request and response, including the headers, body, and timing information. It then publishes this data as a `TraceEvent` to the Redis `trace.events` stream.
4.  **Forwarding:** After recording the interaction, the proxy forwards the original request to the intended destination (e.g., the real Stripe API). The response from the server is then routed back through the proxy to your application.

This entire process is transparent to your application. It simply sees a normal HTTP(S) request and response cycle, while TraceLab captures a complete record of the interaction in the background.

To use the proxy, simply set the `HTTP_PROXY` and `HTTPS_PROXY` environment variables to point to the `sdk-proxy` service:

```bash
export HTTP_PROXY=http://localhost:8888
export HTTPS_PROXY=http://localhost:8888
```

Any application that respects these environment variables will have its traffic automatically recorded by TraceLab.

## FUTURE THINGS

- **Record & Replay:** The real power of TraceLab lies in its ability to replay executions to check for regressions. A replay re-executes the original application command in an identical, sandboxed Docker container. All of its HTTP/S traffic is routed through a dedicated proxy, which records a new set of trace events. The new execution appears on the timeline, allowing you to manually compare it with the original run to identify any changes or regressions in your application's behavior.
- **Chaos Engineering:** Injecting faults and latency into the replays to test the resilience and retry logic of the agents against flaky vendors and network issues.
- **CI Guardrails:** Codifying replay specifications and run them in your CI/CD pipeline to prevent regressions and ensure the agent's behavior doesn't drift over time.
