"use client";

import Link from 'next/link';
import { useState, useEffect } from 'react';

interface Execution {
  id: string;
  status: string;
  started_at: string;
}

async function getExecutions(workflowId: string): Promise<Execution[]> {
  const apiUrl = process.env.NEXT_PUBLIC_API_URL || 'http://localhost:8000';
  try {
    const res = await fetch(`${apiUrl}/api/v1/executions/?workflow_id=${workflowId}`, { cache: 'no-store' });
    if (!res.ok) {
      console.error('Failed to fetch executions');
      return [];
    }
    return res.json();
  } catch (error) {
    console.error('Failed to fetch executions:', error);
    return [];
  }
}

export default function ExecutionsPage({ params }: { params: { workflow_id: string } }) {
  const [executions, setExecutions] = useState<Execution[]>([]);

  useEffect(() => {
    const fetchExecutions = async () => {
      const data = await getExecutions(params.workflow_id);
      setExecutions(data);
    };
    fetchExecutions();
  }, [params.workflow_id]);

  const handleReplay = async (executionId: string) => {
    const apiUrl = process.env.NEXT_PUBLIC_API_URL || 'http://localhost:8000';
    try {
      const res = await fetch(`${apiUrl}/api/v1/replay/${executionId}`, {
        method: 'POST',
        headers: {
          'Content-Type': 'application/json',
        },
        body: JSON.stringify({ mode: 'deterministic' }),
      });
      if (res.ok) {
        alert(`Replay started for execution ${executionId}`);
      } else {
        alert(`Failed to start replay for execution ${executionId}`);
        console.error('Failed to start replay:', await res.text());
      }
    } catch (error) {
      alert(`Failed to start replay for execution ${executionId}`);
      console.error('Failed to start replay:', error);
    }
  };


  return (
    <main className="container mx-auto p-8">
      <h1 className="text-3xl font-bold mb-6">Executions for Workflow {params.workflow_id}</h1>
      <ul className="space-y-4">
        {executions.length > 0 ? (
          executions.map((execution) => (
            <li key={execution.id} className="p-4 border rounded-lg flex justify-between items-center">
              <Link href={`/workflows/${params.workflow_id}/executions/${execution.id}`} className="text-blue-600 hover:underline">
                Execution {execution.id} - {execution.status}
              </Link>
              <button
                onClick={() => handleReplay(execution.id)}
                className="bg-blue-500 hover:bg-blue-700 text-white font-bold py-2 px-4 rounded"
              >
                Replay
              </button>
            </li>
          ))
        ) : (
          <p>No executions found.</p>
        )}
      </ul>
    </main>
  );
}
