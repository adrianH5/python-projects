"""Vector store module for semantic similarity search using FAISS.

Provides efficient similarity search over document embeddings with metadata support.
"""

import logging
from typing import List, Dict, Any, Union
import pickle
from pathlib import Path

import numpy as np
import faiss


class FaissVectorStore:
    """FAISS-based vector store for efficient similarity search.

    Stores embeddings along with metadata for retrieval of semantically
    similar text chunks.
    """

    def __init__(
        self,
        dimension: int,
        index_type: str = "IndexFlatIP",
        normalize_vectors: bool = True,
    ):
        """Initialize FAISS index.

        Args:
            dimension: Dimension of embedding vectors.
            index_type: Type of FAISS index ("IndexFlatIP" or "IndexFlatL2").
            normalize_vectors: Whether to normalize vectors before adding.
        """
        logging.info(
            f"Initializing FAISS index: type={index_type}, dimension={dimension}"
        )

        self.dimension = dimension
        self.index_type = index_type
        self.normalize_vectors = normalize_vectors

        # Create the appropriate index
        if index_type == "IndexFlatIP":
            self.index = faiss.IndexFlatIP(dimension)
        elif index_type == "IndexFlatL2":
            self.index = faiss.IndexFlatL2(dimension)
        else:
            raise ValueError(
                f"Unsupported index_type: {index_type}. "
                "Choose 'IndexFlatIP' or 'IndexFlatL2'"
            )

        # Store metadata separately since FAISS only stores vectors
        self.metadata: List[Dict[str, Any]] = []

    def add(self, vectors: np.ndarray, metadata: List[Dict[str, Any]]) -> None:
        """Add vectors and their metadata to the index.

        Args:
            vectors: Array of shape (n_vectors, dimension).
            metadata: List of metadata dicts corresponding to each vector.

        Raises:
            ValueError: If vectors and metadata lengths don't match.
        """
        if len(vectors) != len(metadata):
            raise ValueError(
                f"Vectors and metadata must have same length. "
                f"Got {len(vectors)} vectors and {len(metadata)} metadata items."
            )

        if vectors.shape[1] != self.dimension:
            raise ValueError(
                f"Vector dimension {vectors.shape[1]} doesn't match "
                f"index dimension {self.dimension}"
            )

        # Normalize vectors if requested (for cosine similarity)
        if self.normalize_vectors and self.index_type == "IndexFlatIP":
            vectors = self._normalize_vectors(vectors)

        # Add to FAISS index
        self.index.add(vectors.astype(np.float32))

        # Store metadata
        self.metadata.extend(metadata)

        logging.info(
            f"Added {len(vectors)} vectors to index. Total: {self.index.ntotal}"
        )

    def search(
        self, query_vectors: np.ndarray, k: int = 5, return_scores: bool = True
    ) -> List[List[Dict[str, Any]]]:
        """Search for k most similar vectors.

        Args:
            query_vectors: Query vectors of shape (n_queries, dimension).
            k: Number of nearest neighbors to return.
            return_scores: Whether to include similarity scores in results.

        Returns:
            List of results for each query. Each result is a list of dicts
            containing metadata and optionally similarity scores.
        """
        if len(query_vectors.shape) == 1:
            query_vectors = query_vectors.reshape(1, -1)

        if query_vectors.shape[1] != self.dimension:
            raise ValueError(
                f"Query dimension {query_vectors.shape[1]} doesn't match "
                f"index dimension {self.dimension}"
            )

        # Normalize query vectors if needed
        if self.normalize_vectors and self.index_type == "IndexFlatIP":
            query_vectors = self._normalize_vectors(query_vectors)

        # Perform search
        k = min(k, self.index.ntotal)  # Can't retrieve more than we have
        distances, indices = self.index.search(query_vectors.astype(np.float32), k)

        # Format results
        results = []
        for query_idx in range(len(query_vectors)):
            query_results = []

            for rank, (idx, score) in enumerate(
                zip(indices[query_idx], distances[query_idx])
            ):
                if idx == -1:  # FAISS returns -1 for unfilled results
                    continue

                result = {"metadata": self.metadata[idx], "rank": rank}

                if return_scores:
                    result["score"] = float(score)

                query_results.append(result)

            results.append(query_results)

        return results

    def search_single(
        self, query_vector: np.ndarray, k: int = 5, return_scores: bool = True
    ) -> List[Dict[str, Any]]:
        """Convenience method to search with a single query vector.

        Args:
            query_vector: Single query vector of shape (dimension,).
            k: Number of nearest neighbors to return.
            return_scores: Whether to include similarity scores.

        Returns:
            List of result dicts with metadata and optionally scores.
        """
        results = self.search(query_vector.reshape(1, -1), k, return_scores)
        return results[0]

    def _normalize_vectors(self, vectors: np.ndarray) -> np.ndarray:
        """L2 normalize vectors for cosine similarity.

        Args:
            vectors: Vectors to normalize.

        Returns:
            Normalized vectors.
        """
        norms = np.linalg.norm(vectors, axis=1, keepdims=True)
        # Avoid division by zero
        norms = np.where(norms == 0, 1, norms)
        return vectors / norms

    def save(self, path: Union[str, Path]) -> None:
        """Save the index and metadata to disk.

        Args:
            path: Directory path to save the index.
        """
        path = Path(path)
        path.mkdir(parents=True, exist_ok=True)

        # Save FAISS index
        index_path = path / "faiss.index"
        faiss.write_index(self.index, str(index_path))

        # Save metadata
        metadata_path = path / "metadata.pkl"
        with open(metadata_path, "wb") as f:
            pickle.dump(
                {
                    "metadata": self.metadata,
                    "dimension": self.dimension,
                    "index_type": self.index_type,
                    "normalize_vectors": self.normalize_vectors,
                },
                f,
            )

        logging.info(f"Saved index with {len(self.metadata)} vectors to {path}")

    @classmethod
    def load(cls, path: Union[str, Path]) -> "FaissVectorStore":
        """Load index and metadata from disk.

        Args:
            path: Directory path containing saved index.

        Returns:
            Loaded FaissVectorStore instance.
        """
        path = Path(path)

        # Load metadata
        metadata_path = path / "metadata.pkl"
        with open(metadata_path, "rb") as f:
            data = pickle.load(f)

        # Create instance
        store = cls(
            dimension=data["dimension"],
            index_type=data["index_type"],
            normalize_vectors=data["normalize_vectors"],
        )

        # Load FAISS index
        index_path = path / "faiss.index"
        store.index = faiss.read_index(str(index_path))
        store.metadata = data["metadata"]

        logging.info(f"Loaded index with {len(store.metadata)} vectors from {path}")

        return store

    def clear(self) -> None:
        """Clear all vectors and metadata from the store."""
        self.index.reset()
        self.metadata.clear()
        logging.info("Cleared vector store")

    def __len__(self) -> int:
        """Return the number of vectors in the store."""
        return self.index.ntotal
