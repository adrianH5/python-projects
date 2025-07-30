"use client";

import { useState, useEffect } from 'react';
import { useRouter } from 'next/navigation';

interface StepEvent {
  id: number;
  idx: number;
  service: string;
  endpoint: string;
  request: any;
  response: any;
  latency_ms: number | null;
  error: string | null;
  ts: string;
}

async function getStepEvents(executionId: string): Promise<StepEvent[]> {
  try {
    const res = await fetch(`http://localhost:8000/api/v1/executions/${executionId}/events`, { cache: 'no-store' });
    if (!res.ok) {
      console.error('Failed to fetch step events');
      return [];
    }
    return res.json();
  } catch (error) {
    console.error('Failed to fetch step events:', error);
    return [];
  }
}

function JsonViewer({ data }: { data: any }) {
  if (!data) return null;
  const [isOpen, setIsOpen] = useState(false);

  return (
    <div>
      <button onClick={() => setIsOpen(!isOpen)} className="text-blue-500 text-sm">
        {isOpen ? 'Hide' : 'Show'} JSON
      </button>
      {isOpen && (
        <pre className="bg-gray-100 p-2 rounded-md text-xs overflow-x-auto">
          {JSON.stringify(data, null, 2)}
        </pre>
      )}
    </div>
  );
}

export default function ExecutionDetailsPage({ params }: { params: { execution_id: string } }) {
  const [events, setEvents] = useState<StepEvent[]>([]);
  const router = useRouter();

  useEffect(() => {
    const fetchEvents = async () => {
      const data = await getStepEvents(params.execution_id);
      setEvents(data);
    };
    fetchEvents();
  }, [params.execution_id]);

  const handleReplay = async () => {
    try {
      const res = await fetch(`http://localhost:8000/api/v1/executions/${params.execution_id}/replay`, {
        method: 'POST',
      });
      if (!res.ok) {
        throw new Error('Failed to start replay');
      }
      const data = await res.json();
      alert(`Replay started successfully! A new workflow named '${data.replay_workflow_name}' will be created.`);
      router.push('/workflows');
    } catch (error) {
      console.error(error);
      alert('An error occurred while starting the replay.');
    }
  };

  return (
    <main className="container mx-auto p-8">
      <div className="flex justify-between items-center mb-6">
        <h1 className="text-3xl font-bold">Execution Details: {params.execution_id}</h1>
        <button
          onClick={handleReplay}
          className="bg-blue-600 hover:bg-blue-700 text-white font-bold py-2 px-4 rounded"
        >
          Replay
        </button>
      </div>
      <div className="overflow-x-auto">
        <table className="min-w-full bg-white border">
          <thead className="bg-gray-200">
            <tr>
              <th className="py-2 px-4 border-b">#</th>
              <th className="py-2 px-4 border-b">Service</th>
              <th className="py-2 px-4 border-b">Endpoint</th>
              <th className="py-2 px-4 border-b">Latency (ms)</th>
              <th className="py-2 px-4 border-b">Request</th>
              <th className="py-2 px-4 border-b">Response</th>
              <th className="py-2 px-4 border-b">Error</th>
              <th className="py-2 px-4 border-b">Timestamp</th>
            </tr>
          </thead>
          <tbody>
            {events.length > 0 ? (
              events.map((event) => (
                <tr key={event.id}>
                  <td className="py-2 px-4 border-b">{event.idx}</td>
                  <td className="py-2 px-4 border-b">{event.service}</td>
                  <td className="py-2 px-4 border-b">{event.endpoint}</td>
                  <td className="py-2 px-4 border-b">{event.latency_ms}</td>
                  <td className="py-2 px-4 border-b"><JsonViewer data={event.request} /></td>
                  <td className="py-2 px-4 border-b"><JsonViewer data={event.response} /></td>
                  <td className="py-2 px-4 border-b text-red-500">{event.error}</td>
                  <td className="py-2 px-4 border-b">{new Date(event.ts).toLocaleString()}</td>
                </tr>
              ))
            ) : (
              <tr>
                <td colSpan={8} className="text-center py-4">No step events found.</td>
              </tr>
            )}
          </tbody>
        </table>
      </div>
    </main>
  );
}
