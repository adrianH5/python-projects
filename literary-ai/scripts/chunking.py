"""Text chunking module for splitting literary texts into processable segments.

Handles intelligent text segmentation while preserving semantic boundaries.
"""

import logging
from typing import List
import re

import nltk
from nltk.tokenize import sent_tokenize

# Download required NLTK data
try:
    nltk.data.find("tokenizers/punkt")
except LookupError:
    nltk.download("punkt", quiet=True)


def split_into_sentences(text: str) -> List[str]:
    """Split text into sentences using NLTK.

    Args:
        text: Input text to split.

    Returns:
        List of sentences.
    """
    try:
        sentences = sent_tokenize(text)
        return sentences
    except Exception as e:
        logging.warning(
            f"Failed to use NLTK sentence tokenizer: {e}. Falling back to regex."
        )
        # Fallback to simple regex-based splitting
        sentences = re.split(r"[.!?]+", text)
        return [s.strip() for s in sentences if s.strip()]


def chunk_by_words(text: str, chunk_size: int = 500) -> List[str]:
    """Split text into chunks of approximately chunk_size words.

    Simple word-based chunking that splits on word boundaries.

    Args:
        text: Text to chunk.
        chunk_size: Target number of words per chunk.

    Returns:
        List of text chunks.
    """
    words = text.split()
    total_words = len(words)
    chunks = []

    for start_idx in range(0, total_words, chunk_size):
        end_idx = min(start_idx + chunk_size, total_words)
        chunk_words = words[start_idx:end_idx]
        chunk = " ".join(chunk_words)
        if chunk:
            chunks.append(chunk)

    return chunks


def chunk_by_sentences(text: str, target_chunk_size: int = 500) -> List[str]:
    """Split text into chunks while preserving sentence boundaries.

    Attempts to create chunks close to target_chunk_size words while
    never splitting in the middle of a sentence.

    Args:
        text: Text to chunk.
        target_chunk_size: Target number of words per chunk.

    Returns:
        List of text chunks with complete sentences.
    """
    sentences = split_into_sentences(text)
    chunks = []
    current_chunk = []
    current_word_count = 0

    for sentence in sentences:
        sentence_word_count = len(sentence.split())

        # If adding this sentence would exceed target, save current chunk
        if (
            current_word_count + sentence_word_count > target_chunk_size
            and current_chunk
        ):
            chunks.append(" ".join(current_chunk))
            current_chunk = []
            current_word_count = 0

        current_chunk.append(sentence)
        current_word_count += sentence_word_count

    # Add the last chunk if it exists
    if current_chunk:
        chunks.append(" ".join(current_chunk))

    return chunks


def chunk_by_paragraphs(text: str, target_chunk_size: int = 500) -> List[str]:
    """Split text into chunks while preserving paragraph boundaries.

    Args:
        text: Text to chunk.
        target_chunk_size: Target number of words per chunk.

    Returns:
        List of text chunks with complete paragraphs.
    """
    # Split by double newlines or multiple spaces indicating paragraphs
    paragraphs = re.split(r"\n\s*\n", text)
    chunks = []
    current_chunk = []
    current_word_count = 0

    for paragraph in paragraphs:
        paragraph = paragraph.strip()
        if not paragraph:
            continue

        paragraph_word_count = len(paragraph.split())

        # If adding this paragraph would exceed target, save current chunk
        if (
            current_word_count + paragraph_word_count > target_chunk_size
            and current_chunk
        ):
            chunks.append("\n\n".join(current_chunk))
            current_chunk = []
            current_word_count = 0

        current_chunk.append(paragraph)
        current_word_count += paragraph_word_count

    # Add the last chunk if it exists
    if current_chunk:
        chunks.append("\n\n".join(current_chunk))

    return chunks


def create_overlapping_chunks(chunks: List[str], overlap_size: int = 50) -> List[str]:
    """Add overlap between consecutive chunks for better context preservation.

    Args:
        chunks: List of text chunks.
        overlap_size: Number of words to overlap between chunks.

    Returns:
        List of chunks with overlapping content.
    """
    if len(chunks) <= 1:
        return chunks

    overlapping_chunks = [chunks[0]]

    for i in range(1, len(chunks)):
        previous_chunk_words = chunks[i - 1].split()
        current_chunk_words = chunks[i].split()

        # Take last overlap_size words from previous chunk
        overlap_words = (
            previous_chunk_words[-overlap_size:]
            if len(previous_chunk_words) > overlap_size
            else previous_chunk_words
        )

        # Combine with current chunk
        overlapped_chunk = " ".join(overlap_words + current_chunk_words)
        overlapping_chunks.append(overlapped_chunk)

    return overlapping_chunks


def chunk_text(
    text: str,
    chunk_size: int = 500,
    chunk_method: str = "sentences",
    add_overlap: bool = False,
    overlap_size: int = 50,
) -> List[str]:
    """Split text into chunks using specified method.

    Main entry point for text chunking with various strategies.

    Args:
        text: Text to chunk.
        chunk_size: Target number of words per chunk.
        chunk_method: Method to use - "words", "sentences", or "paragraphs".
        add_overlap: Whether to add overlap between chunks.
        overlap_size: Number of words to overlap if add_overlap is True.

    Returns:
        List of text chunks.

    Raises:
        ValueError: If chunk_method is not recognized.
    """
    if not text:
        return []

    logging.info(
        f"Chunking text using {chunk_method} method with target size {chunk_size} words"
    )

    chunking_methods = {
        "words": chunk_by_words,
        "sentences": chunk_by_sentences,
        "paragraphs": chunk_by_paragraphs,
    }

    if chunk_method not in chunking_methods:
        raise ValueError(
            f"Unknown chunk method: {chunk_method}. "
            f"Choose from: {', '.join(chunking_methods.keys())}"
        )

    chunking_function = chunking_methods[chunk_method]
    chunks = chunking_function(text, chunk_size)

    if add_overlap and len(chunks) > 1:
        chunks = create_overlapping_chunks(chunks, overlap_size)

    logging.info(f"Created {len(chunks)} chunks")

    return chunks
