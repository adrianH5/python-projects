"""Text normalization module for cleaning extracted literary texts.

Handles common text artifacts from various sources including PDFs and EPUBs.
"""

import re
import unicodedata
import logging


def remove_page_numbers(text: str) -> str:
    """Remove page number artifacts from text.

    Args:
        text: Input text potentially containing page numbers.

    Returns:
        Text with page numbers removed.
    """
    page_number_pattern = r"(\n*\s*Page\s*\d+\s*\n*)"
    return re.sub(page_number_pattern, " ", text, flags=re.IGNORECASE)


def normalize_whitespace(text: str) -> str:
    """Normalize whitespace in text.

    Converts multiple spaces, tabs, and newlines to single spaces.

    Args:
        text: Input text with potentially irregular whitespace.

    Returns:
        Text with normalized whitespace.
    """
    return re.sub(r"\s+", " ", text)


def normalize_unicode(text: str) -> str:
    """Normalize Unicode characters to NFC form.

    Args:
        text: Input text with potentially mixed Unicode forms.

    Returns:
        Text normalized to NFC (Canonical Decomposition, followed by Canonical Composition).
    """
    return unicodedata.normalize("NFC", text)


def remove_scanning_artifacts(text: str) -> str:
    """Remove common scanning artifacts from digitized texts.

    Args:
        text: Input text potentially containing scanning artifacts.

    Returns:
        Text with common artifacts removed.
    """
    # Remove hyphenation at line breaks
    text = re.sub(r"(\w+)-\s*\n\s*(\w+)", r"\1\2", text)

    # Remove standalone numbers that might be footnote references
    text = re.sub(r"\b\d{1,3}\b(?!\d)", "", text)

    # Remove multiple consecutive punctuation marks (scanning errors)
    text = re.sub(r"([.!?]){2,}", r"\1", text)

    return text


def normalize_quotes(text: str) -> str:
    """Standardize quotation marks.

    Args:
        text: Input text with mixed quotation styles.

    Returns:
        Text with standardized quotation marks.
    """
    # Convert smart quotes to standard quotes
    quote_replacements = {
        """: '"',
        """: '"',
        "'": "'",
        "'": "'",
        "„": '"',
        "‚": "'",
    }

    for smart_quote, standard_quote in quote_replacements.items():
        text = text.replace(smart_quote, standard_quote)

    return text


def normalize_text(raw_text: str, remove_artifacts: bool = True) -> str:
    """Clean and normalize extracted text.

    Performs comprehensive text cleaning including Unicode normalization,
    whitespace cleanup, and optional artifact removal.

    Args:
        raw_text: Raw extracted text from any source.
        remove_artifacts: Whether to remove scanning artifacts (default: True).

    Returns:
        Cleaned and normalized text.

    Raises:
        ValueError: If input text is empty or None.
    """
    if not raw_text:
        raise ValueError("Input text cannot be empty or None")

    logging.info("Normalizing text...")

    # Apply normalization steps in order
    text = normalize_unicode(raw_text)
    text = normalize_whitespace(text)
    text = normalize_quotes(text)
    text = remove_page_numbers(text)

    if remove_artifacts:
        text = remove_scanning_artifacts(text)

    # Final trim
    text = text.strip()

    if not text:
        logging.warning("Text normalization resulted in empty text")

    return text
