import base64
import logging
import re
from io import BytesIO
from typing import Optional, Dict, Tuple

import numpy as np
from PIL import Image
from playwright.async_api import Page, TimeoutError as PlaywrightTimeoutError
from skimage.metrics import structural_similarity

from app.services.scraper import _capture_full_scroll_screenshot
from app.core.constants import (
    SCREENSHOT_GOTO_TIMEOUT,
    SCREENSHOT_NETWORK_IDLE_WAIT,
    SCREENSHOT_CAPTURE_TIMEOUT,
)

logger = logging.getLogger(__name__)


def prepare_html_for_screenshot(
    html_content: str, asset_url_mapping: Dict[str, str]
) -> str:
    """
    Replaces Shopify Liquid asset URLs with actual presigned URLs for screenshotting.
    Also handles CSS background images.
    """
    liquid_asset_pattern = re.compile(
        r"""{{\s*['"]([^'"]+)['"]\s*\|\s*asset_url\s*}}"""
    )

    def replacer(match):
        asset_filename = match.group(1)
        return asset_url_mapping.get(asset_filename, "")

    processed_html = liquid_asset_pattern.sub(replacer, html_content)

    style_pattern = re.compile(r'style="([^"]*)"')

    def style_replacer(style_match):
        style_content = style_match.group(1)
        processed_style_content = liquid_asset_pattern.sub(replacer, style_content)
        return f'style="{processed_style_content}"'

    processed_html = style_pattern.sub(style_replacer, processed_html)
    return processed_html


async def take_screenshot_of_html(
    page: Page,
    html_content: str,
    job_id: str,
    attempt: int,
    capture_full_page: bool,
    asset_url_mapping: Optional[Dict[str, str]] = None,
) -> Optional[bytes]:
    """Takes a screenshot of the given HTML content using Playwright."""
    try:
        if asset_url_mapping:
            html_content = prepare_html_for_screenshot(html_content, asset_url_mapping)

        if "<head>" in html_content and "</head>" in html_content:
            tailwind_script = '<script src="https://cdn.tailwindcss.com"></script>'
            if tailwind_script not in html_content:
                html_content = html_content.replace(
                    "</head>", f"{tailwind_script}</head>"
                )
        else:
            logger.warning(
                f"Job {job_id}: Could not find <head> to inject Tailwind CDN."
            )

        data_url = f"data:text/html;base64,{base64.b64encode(html_content.encode('utf-8')).decode('utf-8')}"

        await page.goto(
            data_url, wait_until="networkidle", timeout=SCREENSHOT_GOTO_TIMEOUT
        )
        await page.wait_for_timeout(SCREENSHOT_NETWORK_IDLE_WAIT)

        if capture_full_page:
            context = f"Job {job_id} Att {attempt} - Generated HTML (Full)"
            return await _capture_full_scroll_screenshot(page, context)
        else:
            return await page.screenshot(
                type="png",
                full_page=False,
                timeout=SCREENSHOT_CAPTURE_TIMEOUT,
                animations="disabled",
            )
    except PlaywrightTimeoutError as e:
        logger.error(
            f"Job {job_id} Att {attempt}: Playwright timeout during screenshot: {e}",
            exc_info=False,
        )
    except Exception as e:
        logger.error(
            f"Job {job_id} Att {attempt}: Playwright error during screenshot: {e}",
            exc_info=True,
        )
    return None


def _load_and_prepare_images_for_comparison(
    img_bytes1: bytes, img_bytes2: bytes
) -> Tuple[np.ndarray, np.ndarray]:
    """Loads images from bytes, resizes them to common dimensions, and converts to numpy arrays."""
    img1 = Image.open(BytesIO(img_bytes1)).convert("RGB")
    img2 = Image.open(BytesIO(img_bytes2)).convert("RGB")

    w, h = min(img1.width, img2.width), min(img1.height, img2.height)
    img1_resized = img1.resize((w, h), Image.Resampling.LANCZOS)
    img2_resized = img2.resize((w, h), Image.Resampling.LANCZOS)

    return np.array(img1_resized), np.array(img2_resized)


def _create_heatmap_from_ssim_diff(
    diff_img: np.ndarray, base_img_arr: np.ndarray
) -> bytes:
    """Generates a PNG heatmap from an SSIM difference image."""
    # The SSIM diff image has values from -1 to 1. Normalize to 0-1.
    diff_norm = (diff_img + 1) / 2
    # Invert to highlight differences (1 - similarity), scale to 0-255.
    heatmap_intensity = ((1 - diff_norm) * 255).astype(np.uint8)

    # Ensure heatmap is 3-channel RGB
    if heatmap_intensity.ndim == 2:
        heatmap_intensity_rgb = np.stack([heatmap_intensity] * 3, axis=-1)
    else:
        heatmap_intensity_rgb = heatmap_intensity

    # Create a red heatmap image on a black background
    heatmap_arr = np.zeros_like(base_img_arr)
    heatmap_arr[..., 0] = heatmap_intensity_rgb[..., 0]  # Set the red channel
    heatmap_pil = Image.fromarray(heatmap_arr)

    with BytesIO() as bio:
        heatmap_pil.save(bio, "PNG")
        return bio.getvalue()


def calculate_ssim_and_heatmap(
    orig_bytes: bytes, cloned_bytes: bytes, job_id: str, att: int
) -> Tuple[float, Optional[bytes]]:
    """
    Calculates the Structural Similarity Index (SSIM) and generates a diff heatmap.
    This implementation uses the scikit-image library for the core SSIM calculation.
    """
    try:
        arr1, arr2 = _load_and_prepare_images_for_comparison(orig_bytes, cloned_bytes)

        ssim_score, diff_img = structural_similarity(
            arr1, arr2, channel_axis=-1, full=True, data_range=255
        )
        logger.info(f"Job {job_id} Att {att}: SSIM: {ssim_score:.4f}")

        heatmap_bytes = _create_heatmap_from_ssim_diff(diff_img, arr1)

        return float(ssim_score), heatmap_bytes
    except Exception as e:
        logger.error(
            f"Job {job_id} Att {att}: SSIM/heatmap calculation error: {e}",
            exc_info=True,
        )
        return 0.0, None
