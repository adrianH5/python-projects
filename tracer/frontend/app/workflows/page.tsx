"use client";

import Link from 'next/link';
import { useState, useEffect } from 'react';

interface Workflow {
  id: string;
  name: string;
}

async function getWorkflows(): Promise<Workflow[]> {
  try {
    // The URL must be accessible from the client's browser.
    const res = await fetch('http://localhost:8000/api/v1/workflows/', { cache: 'no-store' });
    if (!res.ok) {
      console.error('Failed to fetch workflows');
      return [];
    }
    return res.json();
  } catch (error) {
    console.error('Failed to fetch workflows:', error);
    return [];
  }
}

export default function WorkflowsPage() {
  const [workflows, setWorkflows] = useState<Workflow[]>([]);

  const fetchWorkflows = async () => {
    const data = await getWorkflows();
    setWorkflows(data);
  };

  useEffect(() => {
    fetchWorkflows();
  }, []);

  const handleDeleteAll = async () => {
    if (!confirm('Are you sure you want to delete all runs? This action cannot be undone.')) {
      return;
    }

    try {
      const res = await fetch('http://localhost:8000/api/v1/workflows/', {
        method: 'DELETE',
      });

      if (!res.ok) {
        throw new Error('Failed to delete workflows');
      }

      // Refresh the list of workflows on the page
      await fetchWorkflows();
      alert('All workflows deleted successfully.');
    } catch (error) {
      console.error(error);
      alert('An error occurred while deleting workflows.');
    }
  };

  return (
    <main className="container mx-auto p-8">
      <div className="flex justify-between items-center mb-6">
        <h1 className="text-3xl font-bold">Workflows</h1>
        <button
          onClick={handleDeleteAll}
          className="bg-red-600 hover:bg-red-700 text-white font-bold py-2 px-4 rounded"
        >
          Delete All Runs
        </button>
      </div>
      <ul className="space-y-4">
        {workflows.length > 0 ? (
          workflows.map((workflow) => (
            <li key={workflow.id} className="p-4 border rounded-lg">
              <Link href={`/workflows/${workflow.id}/executions`} className="text-blue-600 hover:underline">
                {workflow.name}
              </Link>
            </li>
          ))
        ) : (
          <p>No workflows found.</p>
        )}
      </ul>
    </main>
  );
}
