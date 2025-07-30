import { createClient } from 'redis';

let redisClient: any;
let workflowName: string | undefined;
let serviceName: string | undefined;

interface InitOptions {
  workflowName: string;
  serviceName: string;
  redisUrl?: string;
  tags?: Record<string, string>;
}

export function init(options: InitOptions) {
  workflowName = options.workflowName || process.env.TRACE_WORKFLOW_NAME;
  serviceName = options.serviceName || process.env.TRACE_SERVICE_NAME;
  const redisUrl = options.redisUrl || process.env.TRACE_REDIS_URL || 'redis://redis:6379/0';
  redisClient = createClient({ url: redisUrl });
  redisClient.connect();
}

// In a real SDK, you would patch global fetch and other libraries here.
// For this example, we'll just provide a trace function.

export async function trace<T>(name: string, fn: () => Promise<T>): Promise<T> {
  const traceEvent = {
    workflow_name: workflowName,
    service_name: serviceName,
    endpoint: name,
  };
  if (redisClient) {
    await redisClient.xAdd('trace.events', '*', { data: JSON.stringify(traceEvent) });
  }
  return fn();
}
