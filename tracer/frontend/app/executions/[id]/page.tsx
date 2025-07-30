import { Suspense } from 'react';

interface StepEvent {
  id: number;
  service: string;
  endpoint: string;
  ts: string;
}

async function getStepEvents(executionId: string): Promise<StepEvent[]> {
  const res = await fetch(`http://api:8000/api/v1/executions/${executionId}/events/`, { cache: 'no-store' });
  if (!res.ok) {
    throw new Error('Failed to fetch step events');
  }
  return res.json();
}

export default async function ExecutionPage({ params }: { params: { id: string } }) {
  const stepEvents = await getStepEvents(params.id);

  return (
    <main className="container mx-auto p-8">
      <h1 className="text-3xl font-bold mb-6">Execution {params.id}</h1>
      <div className="bg-gray-100 p-8 rounded-lg">
        <h2 className="text-2xl font-bold mb-4">Step Events</h2>
        <ul className="space-y-2">
          {stepEvents.map((event) => (
            <li key={event.id} className="p-2 border-b">
              {event.ts}: {event.service} - {event.endpoint}
            </li>
          ))}
        </ul>
      </div>
    </main>
  );
}
