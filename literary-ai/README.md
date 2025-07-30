# Literary Analysis Pipeline

## Outputs

Normalized text in data/processed/

Embeddings in output/embeddings/

Intermediate Summaries (one per book) in output/reports/intermediate_summaries/

Final Report in output/reports/final_report.txt

Logs: The pipeline writes logs to output/logs/pipeline.log. Check this file for any errors or warnings.

## Overview

This pipeline ingests multiple novels, analyzes a given theme, and produces a
comparative book report with citations. It integrates:

- Data ingestion (PDF/EPUB/XML)
- Normalization to clean text
- Chunking to respect LLM context limits
- Embedding + FAISS-based semantic retrieval
- Knowledge Graph construction
- Multi-Agent approach for summarizing, analyzing, critiquing, and refining text
- Report Generation
- Self-Refinement loops

Project Structure

```bash
book_isolation_pipeline/
├── README.md                  # (This document)
├── requirements.txt           # Python dependencies
├── config.yaml                # Configuration (models, chunk size, etc.)
├── data/
│   ├── raw/                   # Original PDFs, EPUBs, XMLs
│   │   ├── book1.pdf
│   │   ├── book2.epub
│   │   └── book3.xml
│   └── processed/             # Normalized text files
│       ├── book1_normalized.txt
│       ├── book2_normalized.txt
│       └── book3_normalized.txt
├── output/
│   ├── embeddings/            # FAISS indices or other vector store artifacts
│   ├── knowledge_graph/       # GraphML or similar for KG
│   ├── logs/                  # Pipeline logs
│   └── reports/               # Summaries, final report, evaluation
│       ├── intermediate_summaries/
│       │   ├── book1_summary.txt
│       │   ├── book2_summary.txt
│       │   └── book3_summary.txt
│       ├── final_report.txt
├── scripts/
│   ├── data_ingestion.py
│   ├── data_normalization.py
│   ├── chunking.py
│   ├── embedding.py
│   ├── vector_store.py
│   ├── knowledge_graph.py
│   ├── multi_agent.py
│   ├── summary_generation.py
│   ├── final_report.py
│   └── main.py               # Main orchestration
├── tests/                    # Tests
└── run_pipeline.sh           # Simple bash script to run everything
```

Features

1. Data Ingestion
   Ingest multiple book file formats without manual intervention.

PDF parsing with PyMuPDF (fitz).
EPUB parsing with ebooklib.
XML parsing with Python’s ElementTree or lxml.

2. Normalization
   Produce clean, standardized text from each novel.

Remove line breaks, page numbers, scanning artifacts.
Unify whitespace and punctuation .
Store normalized text in data/processed/.
Raw text can contain unwanted noise (page headers, weird spacing, inconsistent quotes). Normalizing ensures a consistent representation for downstream tasks .

3. Chunking
   Respect LLM context limits and create meaningful segments.

Use a simple approach to split text by word count (e.g., ~500 words).
Each chunk is self-contained.
Large language models often have token limits. Breaking the text into smaller “chunks” ensures we can embed or feed them to the model in a retrieval-augmented way.

4. Embedding
   Transform text chunks into semantic vectors for retrieval.

SentenceTransformers (e.g., all-MiniLM-L6-v2) or OpenAI embeddings (text-embedding-ada-002).
The pipeline uses a dedicated Python class (EmbeddingModel).
Text embeddings capture semantic meaning, enabling similarity search.

5. Vector Store with FAISS
   Efficient similarity search on embedded chunks.

We want to quickly retrieve the top chunks relevant to a theme. FAISS is robust and widely used for local deployments.

6. Knowledge Graph (Optional)
   Provide additional structure for advanced logic/fact-checking.

networkx to build a stub knowledge graph of relationships. The pipeline saves the graph as .graphml files.
A knowledge graph can help detect inconsistencies, track character interactions, or be used in symbolic logic checks

7. Multi-Agent Pipeline
   Decompose analysis into specialized roles for better structure and clarity.

Agents:

SummarizerAgent: Summarizes each relevant excerpt, adding inline citations.
ThematicAgent: Focuses on the theme (e.g. “social isolation”), preserves citations.
CriticAgent: Reviews for coherence, completeness, suggests improvements.
ModeratorAgent: Merges suggestions into a refined analysis.
Each agent is a separate LLM call with specialized prompts, ensuring role-based improvements.

Splitting tasks among specialized prompts often yields more coherent and less hallucinated results. Each agent’s output is refined before the final text is produced.

8. Report Generation
   Produce a final multi-paragraph essay comparing the books on the chosen theme.

Data: The final pipeline stage merges the per-book summaries into a comprehensive report.
Citations: The final text references inline citations from the chunk-level analysis, e.g. (BookTitle, chunk 3).
The pipeline instructs the LLM to produce a standard essay format (thesis, body, conclusion).

9. Self-Refinement
   Improve text coherence and correctness by letting the LLM critique/rewrite its own output.

The pipeline calls self_refine_report once or multiple times, prompting the LLM to fix any issues or expand where needed.
A single-pass generation might have mistakes or incomplete reasoning. Refinement loops often yield higher-quality, more thorough outputs.

## Usage

Install dependencies:

```bash
pip install -r requirements.txt
```

All pipeline parameters are set in config.yaml:

```yaml
data:
  raw_dir: "data/raw"
  processed_dir: "data/processed"

output:
  embeddings_dir: "output/embeddings"
  knowledge_graph_dir: "output/knowledge_graph"
  logs_dir: "output/logs"
  reports_dir: "output/reports"

models:
  embedding_model: "sentence-transformers/all-MiniLM-L6-v2"
  llm_model_engine_summary: "gpt-4o" # Model used to generate intermediary summaries
  llm_model_engine_final_report: "gpt-4.5-preview" # Model used to generate final comparative report

llm_settings:
  OPENAI_API_KEY: "<REMOVED>" # probably should move this to environment variable in .zsh
  temperature: 0.3
  max_tokens: 1024

vector_store:
  faiss_index_type: "IndexFlatIP"

pipeline:
  chunk_size: 500 # approx tokens or words per chunk
  top_k: 10
  theme_query: "excerpts about social isolation, loneliness, alienation"
  enable_knowledge_graph: true
  enable_multi_agent: true
  enable_self_refinement: true
  enable_factcheck: true
```

- chunk_size controls how many words go into each chunk.
- top_k is how many chunks to retrieve per book.
- theme_query is the search query representing the theme (e.g. “social isolation”).
- enable_knowledge_graph toggles the KG building step.
- enable_self_refinement toggles the iterative refinement loops.

Usage & Running the Pipeline
Place your books in data/raw/. Supported formats: .pdf, .epub, .xml, plus fallback to textract.
Edit config.yaml to add your OpenAI API key (or adapt for your chosen LLM provider).
Run the pipeline:

```bash
./run_pipeline.sh
```

or

```bash
python -m scripts.main config.yaml
```

## Future stuff to do possibly (not sure if will have time to complete)

Hybrid Search: Combine BM25 with FAISS for improved retrieval of thematically relevant chunks.

Build evaluation model, currently does not fully implement citation checking. Integrate or fine-tune FactCC / SummaC or use a combination of NLI and embedding similarity.

Add more tests!
