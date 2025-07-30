import logging
import re
import networkx as nx
import torch
from tqdm import tqdm
from transformers import AutoTokenizer, AutoModelForSeq2SeqLM


class RebelExtractor:
    """
    A wrapper that uses the Babelscape/rebel-large model for OpenIE triple extraction.
    Produces (subject, relation, object) tuples to store in a knowledge graph.
    """

    def __init__(
        self, model_name="Babelscape/rebel-large", device=None, max_length=512
    ):
        self.tokenizer = AutoTokenizer.from_pretrained(model_name)
        self.model = AutoModelForSeq2SeqLM.from_pretrained(model_name)
        if device is None:
            self.device = "cuda" if torch.cuda.is_available() else "cpu"
        else:
            self.device = device
        self.model.to(self.device)
        self.model.eval()
        self.max_length = max_length
        logging.info(
            f"ReBEL extractor initialized on device={self.device} with model={model_name}"
        )

    def extract_triples_from_text(self, text: str):
        """
        Takes a text string, runs the ReBEL model to extract (subj, rel, obj) triples.
        Returns a list of tuples [(subject, relation, object), ...]
        """
        # Tokenize input
        inputs = self.tokenizer(
            text, return_tensors="pt", truncation=True, max_length=self.max_length
        ).to(self.device)

        # Generate
        generated_tokens = self.model.generate(
            **inputs,
            max_length=256,
            num_beams=3,
            length_penalty=1.0,
            early_stopping=True,
        )

        # Decode
        decoded_text = self.tokenizer.decode(
            generated_tokens[0], skip_special_tokens=True
        )

        # Parse the T5-style output to get triples
        triples = self._postprocess_rebel_output(decoded_text)
        return triples

    def _postprocess_rebel_output(self, rebel_output: str):
        """
        Parse ReBEL model's text output into (subject, relation, object) triples.
        """
        pattern = r"subject\d*:\s*(.*?)\s*;\s*relation\d*:\s*(.*?)\s*;\s*object\d*:\s*(.*?)\s*(?:;|$)"
        matches = re.findall(pattern, rebel_output, re.DOTALL)

        triples = []
        for match in matches:
            subj, rel, obj = match
            subj = subj.strip()
            rel = rel.strip()
            obj = obj.strip()
            if subj and rel and obj:
                triples.append((subj, rel, obj))
        return triples


def build_knowledge_graph(
    text: str,
    book_title: str = "Unknown Book",
    chunk_size: int = 512,
    model_name="Babelscape/rebel-large",
    device=None,
    max_length=512,
) -> nx.DiGraph:
    """
    Splits the text into smaller chunks (to avoid exceeding model limits),
    extracts triples using the ReBEL approach, and builds a directed knowledge graph.

    :param text: Raw text from which to extract relations.
    :param book_title: (optional) name of the book, for logging.
    :param chunk_size: Approx max chunk size in characters (or tokens) for each pass.
    :param model_name: The Hugging Face model to load for relation extraction.
    :param device: 'cuda' or 'cpu'. If None, auto-detect.
    :param max_length: Max tokens for the ReBEL model input.

    :return: A networkx DiGraph with edges labeled by 'relation'.
    """
    logging.info(f"Building knowledge graph for {book_title} using ReBEL...")

    # Initialize the model/extractor
    extractor = RebelExtractor(
        model_name=model_name, device=device, max_length=max_length
    )

    # Split into sentence-like chunks, currently uses .
    sentences = text.split(". ")
    current_chunk = []
    char_count = 0
    chunks = []
    for s in sentences:
        s = s.strip()
        if char_count + len(s) < chunk_size:
            current_chunk.append(s)
            char_count += len(s)
        else:
            # finalize the current chunk
            chunks.append(". ".join(current_chunk))
            current_chunk = [s]
            char_count = len(s)
    if current_chunk:
        chunks.append(". ".join(current_chunk))

    G = nx.DiGraph()

    for i, chunk in enumerate(tqdm(chunks, desc=f"KG building for {book_title}")):
        if not chunk.strip():
            continue
        try:
            # Extract relations from this chunk
            triples = extractor.extract_triples_from_text(chunk)
            for subj, rel, obj in triples:
                if subj not in G:
                    G.add_node(subj, type="entity")
                if obj not in G:
                    G.add_node(obj, type="entity")
                G.add_edge(subj, obj, relation=rel)
        except Exception as e:
            logging.warning(f"Error extracting from chunk {i}: {e}")
            continue

    logging.info(
        f"Finished building KG for {book_title}. Nodes: {len(G.nodes)}, Edges: {len(G.edges)}"
    )
    return G


def save_knowledge_graph(graph: nx.DiGraph, output_path: str):
    """
    Saves the knowledge graph to a file (e.g. GraphML).
    """
    nx.write_graphml(graph, output_path)
    logging.info(f"Knowledge graph saved to {output_path}")
