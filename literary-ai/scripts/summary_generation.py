import logging
from scripts.multi_agent import multi_agent_collaboration


def generate_book_summary(
    book_title,
    vector_store,
    embedding_model,
    theme_query,
    api_key,
    chunk_texts,
    top_k=5,
    model_to_use="gpt-4o",
):
    """
    1) Embed a query describing 'social isolation' theme.
    2) Retrieve top-k relevant chunks from the vector store.
    3) Summarize each chunk with multi-agent approach (now adding citations).
    4) Combine those chunk-level analyses into a single cohesive summary.
    """
    logging.info(f"Generating summary for {book_title} on theme: {theme_query}")
    query_embedding = embedding_model.embed_texts([theme_query])
    # search
    results = vector_store.search(query_embedding, k=top_k)[0]

    final_paragraphs = []
    for r in results:
        chunk_meta = r["metadata"]
        chunk_index = chunk_meta["chunk_index"]
        excerpt_text = chunk_texts[chunk_index]

        # pass book_title and chunk_index so the SummarizerAgent can cite properly.
        refined_analysis = multi_agent_collaboration(
            excerpt_text=excerpt_text,
            book_title=book_title,
            chunk_index=chunk_index,
            api_key=api_key,
            temperature=0.3,
            model_to_use=model_to_use,
        )
        final_paragraphs.append(refined_analysis)

    # Combine all chunk analyses into a bigger summary of the book
    combined_summary = "\n\n".join(final_paragraphs)
    return combined_summary
