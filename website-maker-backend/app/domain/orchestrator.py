import asyncio
import base64
import hashlib
import logging
import time
import traceback
from typing import Dict, Any, Tuple, Optional, List

import httpx
from playwright.async_api import async_playwright, Browser, Page

from app.core.config import settings, ModelProviderEnum
from app.schemas.job import JobStatus
from app.services.scraper import scrape as perform_scrape
from app.domain.dom_hasher import mine_components
from app.domain.token_extractor import extract_tokens
from app.services.storage import minio_put_object
from app.services.redis import update_job_status
from app.services.assets import download_and_store_images
from app.services.llm import (
    call_for_image_description,
    call_for_html_generation,
    get_effective_model_provider,
)
from app.domain.prompt_builder import (
    get_image_description_prompt,
    get_initial_draft_prompt,
    get_refinement_prompt,
)
from app.domain.image_processor import (
    take_screenshot_of_html,
    calculate_ssim_and_heatmap,
)

logger = logging.getLogger(__name__)


def _prepare_prompt_pack(
    orig_url: str,
    tokens: Dict,
    components: Dict,
    sample_data: List[Dict],
    major_sections: List[Dict],
) -> Dict[str, Any]:
    """Compresses scraped data into a dictionary for prompts."""
    comp_map = components.get("all_unique_components_map", {})
    summary = [f"Found {len(comp_map)} unique component types."]
    for _, comp_def in list(comp_map.items())[:10]:
        attrs = "; ".join([f"{k}='{v}'" for k, v in comp_def.get("attrs", {}).items()])
        summary.append(
            f"- <{comp_def.get('tag')}> Attrs: [{attrs}], Children: {len(comp_def.get('children_ids',[]))}"
        )

    return {
        "original_url": orig_url,
        "design_tokens": tokens,
        "components_summary": "\n".join(summary),
        "sample": sample_data,
        "major_sections": major_sections,
        "asset_mapping": {},
    }


async def _generate_initial_draft(
    job_id: str,
    prompt_pack: Dict[str, Any],
    screenshot_b64: Optional[str],
    http_client: httpx.AsyncClient,
) -> str:
    """Generates the initial Liquid HTML draft using the primary LLM."""
    model_provider = get_effective_model_provider(job_id, settings.MODEL)
    if not model_provider:
        return "<html><body><p>Error: No API keys available for any model.</p></body></html>"

    logger.info(f"Job {job_id}: Using {model_provider.value} for initial draft.")

    image_description = None
    if screenshot_b64:
        update_job_status(
            job_id,
            {"message": f"Generating image description with {model_provider.value}..."},
        )
        description_prompt = get_image_description_prompt()
        image_description = await call_for_image_description(
            job_id, model_provider, description_prompt, screenshot_b64, http_client
        )
        if "Error:" in image_description:
            logger.warning(
                f"Job {job_id}: Failed to get image description. Proceeding without it."
            )
            update_job_status(
                job_id, {"message": "Image description failed. Drafting directly..."}
            )
            image_description = None
        else:
            update_job_status(
                job_id, {"message": "Image description generated. Drafting Liquid..."}
            )

    draft_prompt = get_initial_draft_prompt(prompt_pack, image_description)

    return await call_for_html_generation(
        job_id=job_id,
        model_provider=model_provider,
        prompt_text=draft_prompt,
        http_client=http_client,
        is_draft=True,
        screenshot_b64=screenshot_b64,
    )


async def _evaluate_current_draft(
    page: Page,
    html: str,
    job_id: str,
    attempt: int,
    capture_full_page: bool,
    asset_url_mapping: Dict[str, str],
    orig_ss_bytes: bytes,
    previous_ssim: float,
) -> Tuple[float, Optional[bytes], str]:
    """
    Takes a screenshot, calculates SSIM, generates a heatmap, and forms a critique.
    """
    cloned_ss_bytes = await take_screenshot_of_html(
        page, html, job_id, attempt, capture_full_page, asset_url_mapping
    )

    if not cloned_ss_bytes:
        logger.warning(
            f"Job {job_id} Att {attempt}: Failed to screenshot current draft."
        )
        critique = f"Failed to render the current Liquid code. Please review for errors. Previous SSIM was {previous_ssim:.4f}."
        return previous_ssim, None, critique

    cloned_key = f"{job_id}/attempt_{attempt}_cloned.png"
    cloned_ss_url = minio_put_object(cloned_key, cloned_ss_bytes, "image/png")
    update_job_status(job_id, {"cloned_screenshot_url": cloned_ss_url or ""})

    current_ssim, heatmap_bytes = calculate_ssim_and_heatmap(
        orig_ss_bytes, cloned_ss_bytes, job_id, attempt
    )

    if heatmap_bytes:
        heatmap_key = f"{job_id}/attempt_{attempt}_heatmap.png"
        h_url = minio_put_object(heatmap_key, heatmap_bytes, "image/png")
        update_job_status(job_id, {"diff_heatmap_url": h_url or ""})

    critique = f"Current SSIM is {current_ssim:.4f} (target {settings.TARGET_SSIM}). Areas in red on the heatmap need fixing."
    return current_ssim, heatmap_bytes, critique


async def _get_refined_html(
    job_id: str,
    provider: ModelProviderEnum,
    prompt_pack: Dict[str, Any],
    critique: str,
    current_html: str,
    orig_screenshot_b64: str,
    heatmap_b64: Optional[str],
    http_client: httpx.AsyncClient,
) -> Optional[str]:
    """Calls the LLM to get a new version of the HTML based on critique."""
    refinement_prompt = get_refinement_prompt(prompt_pack, critique)
    new_html = await call_for_html_generation(
        job_id,
        provider,
        refinement_prompt,
        http_client,
        is_draft=False,
        current_html=current_html,
        screenshot_b64=orig_screenshot_b64,
        heatmap_b64=heatmap_b64,
    )

    if new_html and "Error:" not in new_html and new_html != current_html:
        return new_html

    logger.warning(
        f"Job {job_id}: LLM failed to provide a new, valid version of HTML. Halting refinement."
    )
    return None


async def _refinement_loop(
    job_id: str,
    orig_ss_bytes: bytes,
    pack: Dict[str, Any],
    init_html: str,
    http_client: httpx.AsyncClient,
    browser: Browser,
    asset_url_mapping: Dict[str, str],
    capture_full_page: bool,
) -> Tuple[str, float, int]:
    """Iteratively refines the HTML to match the original screenshot."""
    html, ssim, attempts = init_html, 0.0, 0
    orig_ss_b64 = base64.b64encode(orig_ss_bytes).decode("utf-8")
    page = await browser.new_page()

    refinement_provider = get_effective_model_provider(job_id, settings.MODEL)
    if not refinement_provider:
        logger.error(
            f"Job {job_id}: No model available for refinement. Returning initial draft."
        )
        await page.close()
        return html, 0.0, 0

    while ssim < settings.TARGET_SSIM and attempts < settings.MAX_REFINEMENT_ATTEMPTS:
        attempts += 1
        update_job_status(
            job_id,
            {
                "state": JobStatus.IN_PROGRESS.value,
                "message": f"Refinement attempt {attempts}. Current SSIM: {ssim:.4f}",
                "attempts": attempts,
                "ssim": ssim,
            },
        )

        current_ssim, heatmap_bytes, critique = await _evaluate_current_draft(
            page,
            html,
            job_id,
            attempts,
            capture_full_page,
            asset_url_mapping,
            orig_ss_bytes,
            ssim,
        )
        ssim = current_ssim

        if ssim >= settings.TARGET_SSIM:
            logger.info(
                f"Job {job_id}: Target SSIM of {settings.TARGET_SSIM} met at attempt {attempts}."
            )
            break

        heatmap_b64 = (
            base64.b64encode(heatmap_bytes).decode("utf-8") if heatmap_bytes else None
        )

        new_html = await _get_refined_html(
            job_id,
            refinement_provider,
            pack,
            critique,
            html,
            orig_ss_b64,
            heatmap_b64,
            http_client,
        )

        if new_html:
            html = new_html
        else:
            break

    await page.close()
    logger.info(
        f"Job {job_id}: Refinement finished. Attempts: {attempts}, Final SSIM: {ssim:.4f}"
    )
    return html, ssim, attempts


async def _async_run_clone(job_id: str, url_str: str, capture_full_page: bool):
    """The async core of the cloning process."""
    update_job_status(
        job_id, {"state": JobStatus.IN_PROGRESS.value, "message": "Scraping..."}
    )
    scraper_bundle = await perform_scrape(url_str, job_id, capture_full_page)

    if not scraper_bundle.html or not scraper_bundle.screenshot_bytes:
        raise ValueError("Scraping failed to retrieve HTML or screenshot.")

    update_job_status(
        job_id, {"message": "Scraping complete. Storing original screenshot."}
    )
    orig_ss_key = f"{job_id}/original_screenshot.png"
    orig_ss_url = minio_put_object(
        orig_ss_key, scraper_bundle.screenshot_bytes, "image/png"
    )
    update_job_status(job_id, {"screenshot_url": orig_ss_url or ""})

    # --- Intelligence Gathering ---
    sample_for_tokens = (
        [list(item.values()) for item in scraper_bundle.sample]
        if scraper_bundle.sample
        else []
    )
    components = mine_components(scraper_bundle.html)
    tokens = extract_tokens(scraper_bundle.screenshot_bytes, sample_for_tokens)
    pack = _prepare_prompt_pack(
        str(scraper_bundle.original_url),
        tokens,
        components,
        scraper_bundle.sample or [],
        scraper_bundle.major_sections or [],
    )

    async with httpx.AsyncClient() as http_client, async_playwright() as p_man:
        # --- Asset Handling ---
        update_job_status(
            job_id,
            {"message": f"Downloading {len(scraper_bundle.image_sources)} images..."},
        )
        url_map, public_url_map = await download_and_store_images(
            job_id, scraper_bundle.image_sources, http_client
        )
        pack["asset_mapping"] = url_map
        update_job_status(
            job_id,
            {"message": f"Downloaded {len(url_map)} images. Generating draft..."},
        )

        # --- Initial Draft ---
        screenshot_b64 = base64.b64encode(scraper_bundle.screenshot_bytes).decode(
            "utf-8"
        )
        draft_html = await _generate_initial_draft(
            job_id, pack, screenshot_b64, http_client
        )
        if "Error:" in draft_html:
            raise ValueError(f"Initial LLM drafting failed: {draft_html}")

        # --- Refinement Loop ---
        update_job_status(job_id, {"message": "Starting visual refinement loop..."})
        browser = await p_man.chromium.launch()
        final_html, final_ssim, total_attempts = await _refinement_loop(
            job_id,
            scraper_bundle.screenshot_bytes,
            pack,
            draft_html,
            http_client,
            browser,
            public_url_map,
            capture_full_page,
        )
        await browser.close()

        # --- Finalization ---
        update_job_status(job_id, {"message": "Persisting final Liquid code..."})
        artifact_key = f"{hashlib.sha256(str(scraper_bundle.original_url).encode('utf-8')).hexdigest()}.liquid"
        artifact_url = minio_put_object(
            artifact_key, final_html.encode("utf-8"), "text/plain"
        )
        if not artifact_url:
            raise ValueError("Failed to persist final refined Liquid code.")

        msg = f"Visual cloning complete. Final SSIM: {final_ssim:.4f}, Attempts: {total_attempts}."
        logger.info(f"Job {job_id}: {msg}")
        update_job_status(
            job_id,
            {
                "state": JobStatus.DONE.value,
                "message": msg,
                "artifact_url": artifact_url,
                "ssim": f"{final_ssim:.4f}",
                "attempts": str(total_attempts),
            },
        )


def run_clone(job_id: str, url_str: str, capture_full_page: bool = True):
    """
    Main entry point for the cloning job, executed by the RQ worker.
    """
    start_tm = time.time()
    logger.info(
        f"Job {job_id}: Starting clone for {url_str}. Full page: {capture_full_page}"
    )
    update_job_status(
        job_id,
        {
            "state": JobStatus.IN_PROGRESS.value,
            "message": "Initializing job...",
            "capture_full_page_setting": str(capture_full_page),
        },
    )

    try:
        asyncio.run(_async_run_clone(job_id, url_str, capture_full_page))
    except Exception as e:
        tb_str = traceback.format_exc()
        logger.error(
            f"Job {job_id}: Unhandled exception in run_clone for URL {url_str}: {e}\n{tb_str}"
        )
        update_job_status(
            job_id,
            {
                "state": JobStatus.ERROR.value,
                "message": f"Orchestrator error: {type(e).__name__}: {e}",
            },
        )
    finally:
        logger.info(
            f"Job {job_id}: Processing finished in {time.time() - start_tm:.2f}s."
        )


if __name__ == "__main__":
    # This allows the module to be imported without running test code.
    logger.info("Orchestrator module loaded. To test, call run_clone() directly.")
