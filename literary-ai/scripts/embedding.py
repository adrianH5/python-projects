"""Text embedding module for converting literary text to semantic vectors.

Uses sentence transformers to create dense vector representations of text chunks.
"""

import logging
from typing import List, Optional
import numpy as np

from sentence_transformers import SentenceTransformer


class EmbeddingModel:
    """Wrapper for sentence transformer models to generate text embeddings.

    Provides a consistent interface for embedding text chunks into vector space
    for semantic similarity search and retrieval.
    """

    def __init__(
        self,
        model_name: str = "all-MiniLM-L6-v2",
        device: Optional[str] = None,
        cache_folder: Optional[str] = None,
    ):
        """Initialize the embedding model.

        Args:
            model_name: Name or path of the sentence transformer model.
            device: Device to run the model on ('cuda', 'cpu', or None for auto).
            cache_folder: Folder to cache downloaded models.
        """
        logging.info(f"Loading embedding model: {model_name}")

        self.model_name = model_name
        self.device = device or "cpu"

        try:
            self.model = SentenceTransformer(
                model_name, device=self.device, cache_folder=cache_folder
            )
            self.embedding_dimension = self.model.get_sentence_embedding_dimension()
            logging.info(
                f"Model loaded successfully. Embedding dimension: {self.embedding_dimension}"
            )
        except Exception as e:
            logging.error(f"Failed to load embedding model: {e}")
            raise

    def embed_text(self, text: str) -> np.ndarray:
        """Embed a single text string.

        Args:
            text: Text to embed.

        Returns:
            Embedding vector as numpy array.
        """
        if not text:
            raise ValueError("Cannot embed empty text")

        embedding = self.model.encode(
            text, show_progress_bar=False, convert_to_numpy=True
        )

        return embedding

    def embed_texts(
        self, texts: List[str], batch_size: int = 32, show_progress: bool = True
    ) -> np.ndarray:
        """Embed multiple text strings.

        Args:
            texts: List of texts to embed.
            batch_size: Number of texts to process at once.
            show_progress: Whether to show progress bar.

        Returns:
            Array of embedding vectors with shape (len(texts), embedding_dim).

        Raises:
            ValueError: If texts list is empty.
        """
        if not texts:
            raise ValueError("Cannot embed empty text list")

        # Filter out empty texts and track indices
        valid_texts = []
        valid_indices = []

        for idx, text in enumerate(texts):
            if text and text.strip():
                valid_texts.append(text)
                valid_indices.append(idx)
            else:
                logging.warning(f"Skipping empty text at index {idx}")

        if not valid_texts:
            raise ValueError("All texts are empty")

        # Generate embeddings
        embeddings = self.model.encode(
            valid_texts,
            batch_size=batch_size,
            show_progress_bar=show_progress,
            convert_to_numpy=True,
        )

        # Create full embedding array with zeros for empty texts
        full_embeddings = np.zeros((len(texts), self.embedding_dimension))
        for i, idx in enumerate(valid_indices):
            full_embeddings[idx] = embeddings[i]

        return full_embeddings

    def get_embedding_dimension(self) -> int:
        """Get the dimension of the embedding vectors.

        Returns:
            Integer dimension of embedding vectors.
        """
        return self.embedding_dimension

    def compute_similarity(
        self, embedding1: np.ndarray, embedding2: np.ndarray
    ) -> float:
        """Compute cosine similarity between two embeddings.

        Args:
            embedding1: First embedding vector.
            embedding2: Second embedding vector.

        Returns:
            Cosine similarity score between -1 and 1.
        """
        # Normalize vectors
        norm1 = np.linalg.norm(embedding1)
        norm2 = np.linalg.norm(embedding2)

        if norm1 == 0 or norm2 == 0:
            return 0.0

        # Compute cosine similarity
        similarity = np.dot(embedding1, embedding2) / (norm1 * norm2)

        return float(similarity)
