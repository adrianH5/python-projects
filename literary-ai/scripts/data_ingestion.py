"""Data ingestion module for extracting text from various file formats.

Supports PDF, EPUB, and XML file formats for literary text extraction.
"""

import os
import logging

import fitz
import ebooklib
from ebooklib import epub
import xml.etree.ElementTree as ET
from bs4 import BeautifulSoup


def extract_pdf(pdf_path: str) -> str:
    """Extract text from a PDF using PyMuPDF.

    Args:
        pdf_path: Path to the PDF file.

    Returns:
        Extracted text content from all pages.

    Raises:
        Exception: If PDF cannot be opened or read.
    """
    text_pages = []

    with fitz.open(pdf_path) as document:
        for page in document:
            page_text = page.get_text()
            if page_text:
                text_pages.append(page_text)

    return "\n".join(text_pages)


def extract_epub(epub_path: str) -> str:
    """Extract text from an EPUB using ebooklib and BeautifulSoup.

    Args:
        epub_path: Path to the EPUB file.

    Returns:
        Extracted text content from all chapters.

    Raises:
        Exception: If EPUB cannot be opened or parsed.
    """
    book = epub.read_epub(epub_path)
    text_content = []

    for document_item in book.get_items_of_type(ebooklib.ITEM_DOCUMENT):
        if document_item.content:
            soup = BeautifulSoup(document_item.content, "html.parser")
            extracted_text = soup.get_text(" ", strip=True)
            if extracted_text:
                text_content.append(extracted_text)

    return "\n".join(text_content)


def extract_xml(xml_path: str) -> str:
    """Extract text from an XML file.

    Specifically looks for content:encoded elements which commonly
    contain the main text content in RSS/content XML formats.

    Args:
        xml_path: Path to the XML file.

    Returns:
        Extracted text content from content:encoded elements.

    Raises:
        ET.ParseError: If XML is malformed.
    """
    tree = ET.parse(xml_path)
    root = tree.getroot()

    namespaces = {"content": "http://purl.org/rss/1.0/modules/content/"}

    encoded_elements = root.findall(".//content:encoded", namespaces)

    text_snippets = []
    for element in encoded_elements:
        if element.text:
            text_snippets.append(element.text)

    return "\n".join(text_snippets)


def ingest_file(file_path: str) -> str:
    """Ingest a file and extract its text content based on file type.

    Automatically detects file type from extension and calls the
    appropriate extraction function.

    Args:
        file_path: Path to the file to ingest.

    Returns:
        Extracted text content.

    Raises:
        ValueError: If file type is not supported.
        FileNotFoundError: If file does not exist.
    """
    if not os.path.exists(file_path):
        raise FileNotFoundError(f"File not found: {file_path}")

    logging.info(f"Ingesting file: {file_path}")

    file_extension = os.path.splitext(file_path)[1].lower()

    extractors = {".pdf": extract_pdf, ".epub": extract_epub, ".xml": extract_xml}

    if file_extension not in extractors:
        supported_formats = ", ".join(extractors.keys())
        raise ValueError(
            f"Unsupported file type: {file_extension}. "
            f"Supported formats: {supported_formats}"
        )

    extractor_function = extractors[file_extension]
    return extractor_function(file_path)
