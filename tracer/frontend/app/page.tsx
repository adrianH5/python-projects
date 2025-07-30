import Link from 'next/link';

export default function Home() {
  return (
    <main className="flex min-h-screen flex-col items-center justify-center p-24">
      <h1 className="text-4xl font-bold mb-8">Welcome to TraceLab</h1>
      <Link href="/workflows" className="text-blue-500 hover:underline">
        View Workflows
      </Link>
    </main>
  );
}
