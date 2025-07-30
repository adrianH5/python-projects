import os
import yaml
import logging

from scripts.data_ingestion import ingest_file
from scripts.data_normalization import normalize_text
from scripts.chunking import chunk_text
from scripts.embedding import EmbeddingModel
from scripts.vector_store import FaissVectorStore
from scripts.knowledge_graph import build_knowledge_graph, save_knowledge_graph
from scripts.summary_generation import generate_book_summary
from scripts.final_report import generate_comparative_report, self_refine_report


def main(config_path="config.yaml"):
    # Setup Logging
    logging.basicConfig(
        filename="output/logs/pipeline.log",
        level=logging.INFO,
        format="%(asctime)s [%(levelname)s] %(message)s",
    )
    logging.info("=== Starting Book Isolation Pipeline ===")

    with open(config_path, "r") as f:
        config = yaml.safe_load(f)

    raw_dir = config["data"]["raw_dir"]
    processed_dir = config["data"]["processed_dir"]

    embeddings_dir = config["output"]["embeddings_dir"]
    kg_dir = config["output"]["knowledge_graph_dir"]
    logs_dir = config["output"]["logs_dir"]
    reports_dir = config["output"]["reports_dir"]

    os.makedirs(embeddings_dir, exist_ok=True)
    os.makedirs(kg_dir, exist_ok=True)
    os.makedirs(logs_dir, exist_ok=True)
    os.makedirs(reports_dir, exist_ok=True)

    model_to_use_summary = config["models"]["llm_model_engine_summary"]
    model_to_use_final = config["models"]["llm_model_engine_final_report"]
    embed_model_name = config["models"]["embedding_model"]
    llm_api_key = config["llm_settings"]["OPENAI_API_KEY"]
    temperature = config["llm_settings"]["temperature"]

    faiss_index_type = config["vector_store"]["faiss_index_type"]

    chunk_size = config["pipeline"]["chunk_size"]
    top_k = config["pipeline"]["top_k"]
    theme_query = config["pipeline"]["theme_query"]
    enable_kg = config["pipeline"]["enable_knowledge_graph"]
    enable_self_ref = config["pipeline"]["enable_self_refinement"]
    enable_factcheck = config["pipeline"]["enable_factcheck"]

    #  ingest & Normalize each book
    book_files = [
        os.path.join(raw_dir, fname)
        for fname in os.listdir(raw_dir)
        if not fname.startswith(".")
    ]

    book_to_chunks = {}
    book_titles = []
    for bf in book_files:
        book_title = os.path.splitext(os.path.basename(bf))[0]
        book_titles.append(book_title)

        raw_text = ingest_file(bf)
        cleaned_text = normalize_text(raw_text)

        # Save to processed file
        processed_path = os.path.join(processed_dir, f"{book_title}_normalized.txt")
        with open(processed_path, "w", encoding="utf-8") as f:
            f.write(cleaned_text)

        # Chunk
        chunks = chunk_text(cleaned_text, chunk_size=chunk_size)
        print(f"Number of chunks: {len(chunks)}")
        book_to_chunks[book_title] = chunks

    #  build Embeddings + vector Stores
    embedding_model = EmbeddingModel(embed_model_name)
    book_vector_stores = {}

    for book_title in book_titles:
        chunks = book_to_chunks[book_title]
        if not chunks:
            logging.warning("No chunks found for this book, Skipping embeddings.")
            continue
        embeddings = embedding_model.embed_texts(chunks)
        dim = embeddings.shape[1]

        vs = FaissVectorStore(dim, index_type=faiss_index_type)
        meta_list = []
        for i, chunk_text_ in enumerate(chunks):
            meta_list.append({"book_title": book_title, "chunk_index": i})
        vs.add(embeddings, meta_list)
        book_vector_stores[book_title] = vs

    #  knowledge graph
    if enable_kg:
        for book_title in book_titles:
            # Combined text from your chunks or raw text
            text_for_kg = " ".join(book_to_chunks[book_title])

            # The output path for this book’s KG
            kg_path = os.path.join(kg_dir, f"{book_title}_relations.graphml")

            # 1) Check if KG file already exists
            if os.path.exists(kg_path):
                print(
                    f"KG for {book_title} already exists at {kg_path}, skipping build."
                )
            else:
                print(f"No existing KG for {book_title}, building now...")
                G = build_knowledge_graph(text_for_kg)
                save_knowledge_graph(G, kg_path)

    #  Summaries per book
    book_summaries = {}
    for book_title in book_titles:
        vs_sum = book_vector_stores[book_title]
        chunks = book_to_chunks[book_title]
        summary = generate_book_summary(
            book_title,
            vs_sum,
            embedding_model,
            theme_query,
            llm_api_key,
            chunks,
            top_k=top_k,
            model_to_use=model_to_use_summary,
        )
        # Save intermediate summary
        summary_path = os.path.join(
            reports_dir, "intermediate_summaries", f"{book_title}_summary.txt"
        )
        os.makedirs(os.path.dirname(summary_path), exist_ok=True)
        with open(summary_path, "w", encoding="utf-8") as f:
            f.write(summary)

        book_summaries[book_title] = summary

    #  Final Comparative Report
    draft_report = generate_comparative_report(
        book_summaries,
        llm_api_key,
        temperature=temperature,
        model_to_use=model_to_use_final,
    )

    # Self-refinement
    final_report = draft_report
    if enable_self_ref:
        final_report = self_refine_report(final_report, llm_api_key)
        # second pass for self refinement
        final_report = self_refine_report(final_report, llm_api_key)

    final_report_path = os.path.join(reports_dir, "final_report.txt")
    with open(final_report_path, "w", encoding="utf-8") as f:
        f.write(final_report)
    logging.info("Final report generated and saved.")

    logging.info("=== Pipeline Complete ===")


if __name__ == "__main__":
    main()
