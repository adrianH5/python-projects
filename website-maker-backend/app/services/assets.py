import asyncio
import hashlib
import logging
import os
import re
from typing import List, Tuple, Dict, Set
from urllib.parse import urlparse

import httpx

from app.services.storage import minio_put_object
from app.core.constants import (
    ASSET_DOWNLOAD_CONCURRENCY,
    ASSET_DOWNLOAD_TIMEOUT,
    MAX_FILENAME_LENGTH,
    FILENAME_RESERVED_CHARS,
)

logger = logging.getLogger(__name__)

# User agent to mimic a common browser
HTTP_CLIENT_HEADERS = {
    "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/125.0.0.0 Safari/537.36",
    "Accept": "image/avif,image/webp,image/apng,image/svg+xml,image/*,*/*;q=0.8",
    "Accept-Encoding": "gzip, deflate, br",
    "Accept-Language": "en-US,en;q=0.9",
}


def sanitize_filename(url: str) -> str:
    """Creates a safe filename from a URL, avoiding common issues."""
    try:
        parsed_url = urlparse(url)
        path = parsed_url.path
        filename = os.path.basename(path) if path else ""

        if not filename:
            return hashlib.md5(url.encode("utf-8")).hexdigest() + ".asset"

        filename = filename.split("?")[0]
        sanitized_filename = re.sub(FILENAME_RESERVED_CHARS, "_", filename)

        if len(sanitized_filename) > MAX_FILENAME_LENGTH:
            name, ext = os.path.splitext(sanitized_filename)
            ext = ext[:10]
            sanitized_filename = name[: MAX_FILENAME_LENGTH - 1 - len(ext)] + ext

        if not sanitized_filename.strip() or sanitized_filename.startswith("."):
            return hashlib.md5(url.encode("utf-8")).hexdigest() + ".asset"

        return sanitized_filename
    except Exception:
        return hashlib.md5(url.encode("utf-8")).hexdigest() + ".asset"


async def download_and_store_images(
    job_id: str, image_urls: List[str], http_client: httpx.AsyncClient
) -> Tuple[Dict[str, str], Dict[str, str]]:
    """
    Downloads images, stores them in MinIO, and returns URL mappings.

    Args:
        job_id: The job ID for namespacing assets.
        image_urls: A list of image URLs to download.
        http_client: An httpx.AsyncClient for making requests.

    Returns:
        A tuple containing two dictionaries:
        1. url_to_filename_map: Maps original URL to new asset filename.
        2. filename_to_public_url_map: Maps new asset filename to its public MinIO URL.
    """
    url_to_filename_map: Dict[str, str] = {}
    filename_to_public_url_map: Dict[str, str] = {}
    processed_filenames: Set[str] = set()
    semaphore = asyncio.Semaphore(ASSET_DOWNLOAD_CONCURRENCY)

    async def download_one(url: str):
        async with semaphore:
            try:
                response = await http_client.get(
                    url,
                    timeout=ASSET_DOWNLOAD_TIMEOUT,
                    follow_redirects=True,
                    headers=HTTP_CLIENT_HEADERS,
                )
                response.raise_for_status()
                asset_data = response.content
                content_type = response.headers.get(
                    "content-type", "application/octet-stream"
                )

                asset_filename = sanitize_filename(url)
                original_asset_filename = asset_filename
                counter = 1
                while asset_filename in processed_filenames:
                    name, ext = os.path.splitext(original_asset_filename)
                    asset_filename = f"{name}_{counter}{ext}"
                    counter += 1
                processed_filenames.add(asset_filename)

                asset_key = f"{job_id}/assets/{asset_filename}"
                asset_public_url = minio_put_object(asset_key, asset_data, content_type)

                if asset_public_url:
                    url_to_filename_map[url] = asset_filename
                    filename_to_public_url_map[asset_filename] = asset_public_url
                    logger.info(
                        f"Job {job_id}: Successfully stored image {url} as {asset_key}"
                    )
                else:
                    logger.warning(
                        f"Job {job_id}: Stored image {asset_key} but failed to get a public URL."
                    )
            except httpx.HTTPStatusError as e:
                logger.warning(
                    f"Job {job_id}: Failed to download image {url}. Status: {e.response.status_code}"
                )
            except Exception as e:
                logger.error(
                    f"Job {job_id}: Error processing image URL {url}: {e}",
                    exc_info=False,
                )

    unique_image_urls = set(filter(None, image_urls))
    download_tasks = [download_one(url) for url in unique_image_urls]
    await asyncio.gather(*download_tasks)
    return url_to_filename_map, filename_to_public_url_map
