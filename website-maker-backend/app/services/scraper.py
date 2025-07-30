import logging
import os
import time
from typing import Optional
import sys
from io import BytesIO
from PIL import Image  # Added for stitching screenshots

import httpx
from pydantic import AnyHttpUrl
from requests_html import HTMLSession
from playwright.async_api import (
    async_playwright,
    TimeoutError as PlaywrightTimeoutError,
    Browser as PlaywrightBrowser,
    Page,
)

from app.schemas.internal import ScraperOutput
from app.core.config import settings, ScraperModeEnum

logger = logging.getLogger(__name__)

os.makedirs(settings.TEMP_DIR, exist_ok=True)

PLAYWRIGHT_SCRIPT_TO_EVALUATE = r"""
async () => {
    // --- Detailed Style Sampling ---
    const sample = Array.from(document.querySelectorAll("*"))
                  .slice(0, 100) // Increased sample size
                  .map(el => {
                      try {
                          const cs = getComputedStyle(el);
                          let classNameStr = el.className;
                          if (typeof classNameStr === 'object' && classNameStr !== null && typeof classNameStr.baseVal === 'string') {
                            classNameStr = classNameStr.baseVal;
                          } else if (typeof classNameStr !== 'string') {
                            classNameStr = '';
                          }
                          // Capture a much richer set of CSS properties
                          return {
                              tagName: el.tagName || '',
                              className: classNameStr || '',
                              fontSize: cs.fontSize || '',
                              fontWeight: cs.fontWeight || '',
                              color: cs.color || '',
                              backgroundColor: cs.backgroundColor || '',
                              margin: cs.margin || '',
                              padding: cs.padding || '',
                              border: cs.border || '',
                              borderRadius: cs.borderRadius || '',
                              boxShadow: cs.boxShadow || '',
                              display: cs.display || '',
                              flexDirection: cs.flexDirection || '',
                              alignItems: cs.alignItems || '',
                              justifyContent: cs.justifyContent || '',
                              lineHeight: cs.lineHeight || '',
                              letterSpacing: cs.letterSpacing || '',
                              textAlign: cs.textAlign || '',
                              textTransform: cs.textTransform || '',
                              textDecoration: cs.textDecoration || '',
                          };
                      } catch (e) {
                          return { tagName: el.tagName || '', className: el.className || '' };
                      }
                  });

    const base = document.baseURI;

    // --- Comprehensive Image Source Extraction ---
    const assetUrls = new Set();
    const addUrl = (url) => {
        if (!url || url.startsWith('data:')) return;
        try {
            assetUrls.add(new URL(url, base).href);
        } catch (e) { /* Ignore invalid URLs */ }
    };

    // 1. From <img> tags (src and srcset)
    document.querySelectorAll('img').forEach(img => {
        if (img.src) addUrl(img.src);
        if (img.srcset) {
            img.srcset.split(',').forEach(part => {
                const url = part.trim().split(' ')[0];
                addUrl(url);
            });
        }
    });

    // 2. From <source> tags inside <picture>
    document.querySelectorAll('picture source').forEach(source => {
        if (source.srcset) {
            source.srcset.split(',').forEach(part => {
                const url = part.trim().split(' ')[0];
                addUrl(url);
            });
        }
    });

    // 3. From <video> poster attributes
    document.querySelectorAll('video').forEach(video => {
        if (video.poster) addUrl(video.poster);
    });

    // 4. From inline style attributes and computed styles
    const urlRegex = /url\((?!['"]?data:)['"]?([^'"\)]+)['"]?\)/g;
    document.querySelectorAll('*').forEach(el => {
        // Check inline style attribute
        const inlineStyle = el.getAttribute('style');
        if (inlineStyle) {
            let match;
            while ((match = urlRegex.exec(inlineStyle)) !== null) {
                addUrl(match[1]);
            }
        }
        // Check computed style (more comprehensive)
        try {
            const computedStyle = getComputedStyle(el);
            const bgImage = computedStyle.getPropertyValue('background-image');
            if (bgImage && bgImage !== 'none') {
                let match;
                while ((match = urlRegex.exec(bgImage)) !== null) {
                    addUrl(match[1]);
                }
            }
        } catch(e) { /* some elements like script tags don't have computed styles */ }
    });
    const unique_image_sources = Array.from(assetUrls);


    // --- Major Section Identification ---
    const major_sections = [];
    const bodyChildren = Array.from(document.body.children);
    const significantChildCount = 3;
    bodyChildren.forEach(child => {
      const tagName = child.tagName.toUpperCase();
      const id = child.id || '';
      const classList = Array.from(child.classList);
      const childElementCount = child.childElementCount;
      const textSnippet = (child.textContent || '').trim().substring(0, 50).replace(/\s+/g, ' ') + ( (child.textContent || '').trim().length > 50 ? '...' : '');
      if (['HEADER', 'FOOTER', 'MAIN', 'NAV', 'ASIDE', 'SECTION'].includes(tagName) || (tagName === 'DIV' && childElementCount >= significantChildCount)) {
        major_sections.push({ tagName: tagName, id: id, classList: classList, childElementCount: childElementCount, textContentSnippet: textSnippet });
      }
    });

    // --- Final Payload ---
    const html = document.documentElement.outerHTML;
    return { html, sample, image_sources: unique_image_sources, major_sections };
}
"""


async def _capture_full_scroll_screenshot(
    page: Page, context_description: str
) -> Optional[bytes]:
    """Captures a full scroll screenshot of the page by scrolling and stitching."""
    logger.info(f"Attempting full page scrolling screenshot ({context_description})...")
    try:
        # Get total scroll height and viewport height
        body_scroll_height = await page.evaluate("document.body.scrollHeight")
        viewport_height = (
            page.viewport_size["height"] if page.viewport_size else 800
        )  # Default if None

        logger.info(
            f"Page scrollHeight: {body_scroll_height}, viewportHeight: {viewport_height} ({context_description})"
        )

        image_parts = []
        current_scroll = 0
        # Scroll by slightly less than viewport to ensure overlap, helps with some fixed elements and stitching later if needed
        scroll_increment = viewport_height * 0.9
        max_scrolls = 25  # Increased safety break
        scroll_count = 0

        initial_scroll_y = await page.evaluate("window.scrollY")
        if initial_scroll_y > 0:  # Ensure we start from the top
            await page.evaluate("window.scrollTo(0, 0)")
            await page.wait_for_timeout(500)  # Wait for scroll to settle

        while current_scroll < body_scroll_height and scroll_count < max_scrolls:
            logger.info(
                f"Taking screenshot part {scroll_count + 1} at scrollY {current_scroll:.0f} / {body_scroll_height} ({context_description})"
            )
            # Ensure the page is scrolled to the correct position before taking the screenshot
            await page.evaluate(f"window.scrollTo(0, {current_scroll})")
            await page.wait_for_timeout(500)  # Allow content to render after scroll

            part_png = await page.screenshot(
                type="png", timeout=20000, animations="disabled"
            )
            if not part_png:
                logger.error(
                    f"Failed to capture screenshot part {scroll_count + 1} ({context_description})"
                )
                return None
            image_parts.append(Image.open(BytesIO(part_png)))

            last_captured_scroll_y = current_scroll
            current_scroll += scroll_increment

            if current_scroll >= body_scroll_height and last_captured_scroll_y < (
                body_scroll_height - viewport_height * 0.1
            ):
                # If we overshot but there's still a significant portion at the bottom, capture the very end
                final_scroll_pos = body_scroll_height - viewport_height
                if (
                    final_scroll_pos > last_captured_scroll_y
                ):  # Avoid re-capturing if already covered
                    logger.info(
                        f"Taking final screenshot part at scrollY {final_scroll_pos:.0f} ({context_description})"
                    )
                    await page.evaluate(f"window.scrollTo(0, {final_scroll_pos})")
                    await page.wait_for_timeout(
                        1000
                    )  # Wait for final scroll and render
                    part_png = await page.screenshot(
                        type="png", timeout=20000, animations="disabled"
                    )
                    if part_png:
                        image_parts.append(Image.open(BytesIO(part_png)))
                break  # Exit loop after attempting to capture the bottom

            scroll_count += 1
            if scroll_count >= max_scrolls:
                logger.warning(
                    f"Reached max_scrolls ({max_scrolls}) for ({context_description}). Screenshot may be incomplete."
                )
                break

        if not image_parts:
            logger.error(f"No screenshot parts captured ({context_description})")
            return None

        # Stitch images
        widths, heights = zip(*(i.size for i in image_parts))
        max_width = (
            image_parts[0].width if image_parts else 1280
        )  # Use width of the first part

        # Simple vertical stacking. More advanced stitching could remove overlaps from fixed headers/footers.
        # For now, the LLM will have to interpret repeated fixed elements.
        total_stitched_height = sum(h for h in heights)

        stitched_image = Image.new("RGB", (max_width, total_stitched_height))
        y_offset = 0
        for part in image_parts:
            stitched_image.paste(part, (0, y_offset))
            y_offset += part.height

        output_buffer = BytesIO()
        stitched_image.save(output_buffer, format="PNG")
        stitched_bytes = output_buffer.getvalue()
        logger.info(
            f"Successfully stitched {len(image_parts)} parts into a full page screenshot. Final size: {len(stitched_bytes)} bytes, Dimensions: {max_width}x{total_stitched_height} ({context_description})"
        )
        return stitched_bytes

    except Exception as e_scroll_shot:
        logger.error(
            f"Error during scrolling screenshot capture ({context_description}): {e_scroll_shot}",
            exc_info=True,
        )
        return None


async def _common_playwright_logic(
    page: Page,
    url_to_scrape: str,
    job_id: str,
    context_description: str,
    capture_full_page: bool = True,
) -> Optional[ScraperOutput]:
    """Shared Playwright logic for navigation, script execution, and screenshot."""
    try:
        logger.info(
            f"Navigating to {url_to_scrape} using {context_description} for job {job_id}..."
        )
        await page.goto(url_to_scrape, wait_until="domcontentloaded", timeout=60000)

        logger.info(
            f"Initial page content loaded. Waiting for network activity to cease for {url_to_scrape}..."
        )
        try:
            # Wait for the network to be idle. This is more reliable than a fixed timeout
            # for pages with heavy client-side rendering or lazy-loaded content.
            await page.wait_for_load_state("networkidle", timeout=15000)
            logger.info(f"Network is idle for {url_to_scrape}.")
        except PlaywrightTimeoutError:
            logger.warning(
                f"Timed out waiting for network idle for {url_to_scrape}. Proceeding anyway."
            )

        # Add a final small delay for any post-network rendering or animations to settle.
        await page.wait_for_timeout(2000)

        logger.info(
            f"Page should be fully loaded. Executing script for {url_to_scrape} ({context_description})..."
        )
        dom_data = await page.evaluate(PLAYWRIGHT_SCRIPT_TO_EVALUATE)
        html_content = dom_data.get("html")
        sample_data = dom_data.get("sample")
        image_sources_data = dom_data.get("image_sources", [])
        major_sections_data = dom_data.get("major_sections", [])

        if not html_content:
            logger.error(
                f"Playwright script execution for {url_to_scrape} ({context_description}) missing HTML."
            )
            return None

        screenshot_bytes_png: Optional[bytes] = None
        if capture_full_page:
            logger.info(
                f"Attempting full page scrolling screenshot for {url_to_scrape} ({context_description})."
            )
            screenshot_bytes_png = await _capture_full_scroll_screenshot(
                page, f"{context_description} - URL: {url_to_scrape[:50]}"
            )
        else:
            logger.info(
                f"Attempting viewport screenshot for {url_to_scrape} ({context_description})."
            )
            try:
                screenshot_bytes_png = await page.screenshot(
                    type="png", full_page=False, timeout=30000, animations="disabled"
                )
            except Exception as e_vp_shot:
                logger.error(
                    f"Error taking viewport screenshot for {url_to_scrape} ({context_description}): {e_vp_shot}",
                    exc_info=True,
                )
                screenshot_bytes_png = None  # Ensure it's None on failure

        if not screenshot_bytes_png:
            logger.error(
                f"Screenshot capture (full_page={capture_full_page}) failed for {url_to_scrape} ({context_description})."
            )
            # We can still return the HTML content even if the screenshot fails
            # The orchestrator will handle the case where screenshot_bytes is empty.
            # So we don't return None here, but let the caller decide.
            pass

        return ScraperOutput(
            html=html_content,
            sample=sample_data or [],
            image_sources=image_sources_data or [],
            major_sections=major_sections_data or [],
            screenshot_bytes=screenshot_bytes_png or b"",
            original_url=AnyHttpUrl(page.url),
        )
    except PlaywrightTimeoutError as e:
        logger.error(
            f"Playwright timeout during {context_description} operation for {url_to_scrape}: {e}"
        )
    except Exception as e:
        logger.error(
            f"Unexpected error during {context_description} Playwright operation for {url_to_scrape}: {e}",
            exc_info=True,
        )
    return None


async def _scrape_with_local_playwright(
    url_to_scrape: str, job_id: str, capture_full_page: bool = True
) -> Optional[ScraperOutput]:
    logger.info(
        f"Attempting to scrape URL via Local Playwright: {url_to_scrape} for job {job_id}, Full Page: {capture_full_page}"
    )
    browser: Optional[PlaywrightBrowser] = None
    # Common launch arguments for stability in Docker/CI environments and to avoid bot detection
    launch_args = [
        "--no-sandbox",
        "--disable-setuid-sandbox",
        "--disable-dev-shm-usage",
        "--disable-accelerated-2d-canvas",
        "--disable-gpu",
        "--disable-http2",  # Explicitly disable HTTP/2 to work around protocol errors
    ]
    try:
        async with async_playwright() as p:
            browser = await p.chromium.launch(args=launch_args)
            context = await browser.new_context(
                user_agent="Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/125.0.0.0 Safari/537.36",
                viewport={"width": 1920, "height": 1080},
                java_script_enabled=True,
                ignore_https_errors=True,
                locale="en-US",
                timezone_id="America/New_York",
            )
            page = await context.new_page()

            output = await _common_playwright_logic(
                page, url_to_scrape, job_id, "Local Playwright", capture_full_page
            )

            await context.close()
            await browser.close()
            browser = None
            return output
    except Exception as e:
        logger.error(
            f"Error during local Playwright scrape for {url_to_scrape}: {e}",
            exc_info=True,
        )
    finally:
        if browser and browser.is_connected():
            logger.info("Closing local Playwright browser in finally block...")
            try:
                await browser.close()
            except Exception as e_close:
                logger.error(f"Error closing local_playwright browser: {e_close}")
    return None


async def _scrape_with_browserbase(
    http_client: httpx.AsyncClient,
    url_to_scrape: str,
    job_id: str,
    capture_full_page: bool = True,
) -> Optional[ScraperOutput]:
    if not settings.BROWSERBASE_KEY or not settings.BROWSERBASE_PROJECT_ID:
        logger.error(
            "BROWSERBASE_KEY or BROWSERBASE_PROJECT_ID not configured. Cannot use Browserbase."
        )
        return None
    logger.info(
        f"Attempting to scrape URL via Browserbase: {url_to_scrape} for job {job_id}"
    )

    session_creation_url = f"{settings.BROWSERBASE_API_URL.rstrip('/')}/sessions"
    session_payload = {
        "projectId": settings.BROWSERBASE_PROJECT_ID,
        "keepAlive": False,
        "browserSettings": {"timeout": 120},
        "userMetadata": {"job_id": job_id},
    }
    headers = {
        "Content-Type": "application/json",
        "X-BB-API-Key": settings.BROWSERBASE_KEY,
    }
    browser_instance = None
    try:
        logger.info(f"Creating Browserbase session for {url_to_scrape}...")
        response = await http_client.post(
            session_creation_url, json=session_payload, headers=headers, timeout=60.0
        )
        response.raise_for_status()
        session_data = response.json()
        connect_url = session_data.get("connectUrl")
        session_id = session_data.get("id")

        if not connect_url:
            logger.error(
                f"Browserbase session creation failed: 'connectUrl' not found. Response: {session_data}"
            )
            return None
        logger.info(
            f"Browserbase session {session_id} created. Connecting Playwright..."
        )

        async with async_playwright() as p:
            browser_instance = await p.chromium.connect_over_cdp(
                connect_url, timeout=60000
            )
            if not browser_instance.contexts:
                logger.error(f"Browserbase session {session_id}: No browser contexts.")
                await browser_instance.close()
                return None
            context = browser_instance.contexts[0]
            page = context.pages[0] if context.pages else await context.new_page()

            output = await _common_playwright_logic(
                page,
                url_to_scrape,
                job_id,
                f"Browserbase (session {session_id})",
                capture_full_page,
            )

            await browser_instance.close()
            browser_instance = None
            return output

    except httpx.HTTPStatusError as e:
        logger.error(
            f"Browserbase API HTTP error: {e.response.status_code} - {e.response.text}"
        )
    except httpx.RequestError as e:
        logger.error(f"Browserbase API request error: {e}")
    except (
        Exception
    ) as e:  # Includes PlaywrightTimeoutError from _common_playwright_logic
        logger.error(f"Error during Browserbase scrape: {e}", exc_info=True)
    finally:
        if browser_instance and browser_instance.is_connected():
            logger.info("Closing Browserbase Playwright connection in finally block...")
            try:
                await browser_instance.close()
            except Exception as e_close:
                logger.error(f"Error closing browser_instance (Browserbase): {e_close}")
    return None


def _scrape_with_requests_html(url_str: str, job_id: str) -> ScraperOutput:
    logger.info(
        f"Attempting to scrape URL via requests_html: {url_str} for job {job_id}"
    )
    session = HTMLSession()
    html_content = ""
    sample_data = []
    final_url = AnyHttpUrl(url_str)
    try:
        r = session.get(url_str, timeout=30)
        r.raise_for_status()
        html_content = (
            r.html.raw_html.decode("utf-8", errors="replace") if r.html.raw_html else ""
        )
        final_url = AnyHttpUrl(str(r.url))
        if r.html:
            for el in r.html.find("*")[:50]:
                class_attr = el.attrs.get("class", "")
                class_name_str = (
                    " ".join(class_attr)
                    if isinstance(class_attr, (tuple, list))
                    else str(class_attr)
                )
                sample_data.append([el.tag, class_name_str, "", "", "", "", ""])
    except Exception as e:
        logger.error(
            f"Error during requests_html scrape for {url_str}: {e}", exc_info=True
        )
    return ScraperOutput(
        html=html_content,
        sample=sample_data,
        image_sources=[],
        major_sections=[],
        screenshot_bytes=b"",
        original_url=final_url,
    )


async def scrape(
    url_str: str, job_id: str, capture_full_page: bool = True
) -> ScraperOutput:  # Added capture_full_page
    logger.info(
        f"Starting scrape for URL: {url_str}, Job ID: {job_id}, Mode: {settings.SCRAPER_MODE.value}, Full Page: {capture_full_page}"
    )
    scraper_output: Optional[ScraperOutput] = None

    # HTML_ONLY mode does not support screenshots, so capture_full_page is irrelevant
    if settings.SCRAPER_MODE == ScraperModeEnum.HTML_ONLY:
        logger.info(f"HTML_ONLY mode: Using requests_html for {url_str}")
        scraper_output = _scrape_with_requests_html(url_str, job_id)
        # Ensure screenshot_bytes is empty for HTML_ONLY mode if it somehow got set
        if scraper_output:
            scraper_output.screenshot_bytes = b""
        # Skip other modes if HTML_ONLY is selected
        if not scraper_output:  # Should always return something from requests_html
            logger.error(
                f"requests_html failed unexpectedly for {url_str}. Returning default empty output."
            )
            return ScraperOutput(
                html="",
                sample=[],
                image_sources=[],
                major_sections=[],
                screenshot_bytes=b"",
                original_url=AnyHttpUrl(url_str),
            )
        logger.info(
            f"Scraping completed (HTML_ONLY) for URL: {url_str}. HTML length: {len(scraper_output.html)}"
        )
        return scraper_output

    if settings.SCRAPER_MODE == ScraperModeEnum.AUTO:
        if settings.BROWSERBASE_KEY and settings.BROWSERBASE_PROJECT_ID:
            logger.info(
                f"AUTO mode: Attempting Browserbase for {url_str}, Full Page: {capture_full_page}"
            )
            async with httpx.AsyncClient() as client:
                scraper_output = await _scrape_with_browserbase(
                    client, url_str, job_id, capture_full_page
                )

        if (
            not scraper_output or not scraper_output.screenshot_bytes
        ):  # Check for screenshot specifically
            if not scraper_output:
                logger.warning(f"Browserbase scrape critically failed for {url_str}.")
            else:
                logger.warning(f"Browserbase returned no screenshot for {url_str}.")
            logger.info(
                f"Falling back to Local Playwright for {url_str}, Full Page: {capture_full_page}"
            )
            scraper_output = await _scrape_with_local_playwright(
                url_str, job_id, capture_full_page
            )

            if not scraper_output or not scraper_output.screenshot_bytes:
                if not scraper_output:
                    logger.warning(
                        f"Local Playwright scrape critically failed for {url_str}."
                    )
                else:
                    logger.warning(
                        f"Local Playwright returned no screenshot for {url_str}."
                    )
                logger.info(
                    f"Falling back to requests_html for {url_str} (no screenshot will be available)."
                )
                scraper_output_html_only = _scrape_with_requests_html(url_str, job_id)
                # Preserve HTML if Playwright failed but requests_html worked
                if (
                    scraper_output
                    and scraper_output.html
                    and not scraper_output_html_only.html
                ):
                    scraper_output_html_only.html = (
                        scraper_output.html
                    )  # Keep potentially better HTML
                scraper_output = scraper_output_html_only
                if scraper_output:
                    scraper_output.screenshot_bytes = b""  # Ensure no screenshot

    elif settings.SCRAPER_MODE == ScraperModeEnum.LOCAL_PLAYWRIGHT:
        logger.info(
            f"LOCAL_PLAYWRIGHT mode: Attempting Local Playwright for {url_str}, Full Page: {capture_full_page}"
        )
        scraper_output = await _scrape_with_local_playwright(
            url_str, job_id, capture_full_page
        )
        if not scraper_output or not scraper_output.screenshot_bytes:
            if not scraper_output:
                logger.warning(
                    f"Local Playwright scrape critically failed for {url_str}."
                )
            else:
                logger.warning(
                    f"Local Playwright returned no screenshot for {url_str}."
                )
            logger.info(
                f"Falling back to requests_html for {url_str} (no screenshot will be available)."
            )
            scraper_output_html_only = _scrape_with_requests_html(url_str, job_id)
            if (
                scraper_output
                and scraper_output.html
                and not scraper_output_html_only.html
            ):
                scraper_output_html_only.html = scraper_output.html
            scraper_output = scraper_output_html_only
            if scraper_output:
                scraper_output.screenshot_bytes = b""

    # This 'else' for invalid SCRAPER_MODE should ideally not be hit if settings are validated.
    # But as a safeguard, it falls back to requests_html.
    elif (
        settings.SCRAPER_MODE != ScraperModeEnum.HTML_ONLY
    ):  # Already handled HTML_ONLY above
        logger.info(f"HTML_ONLY mode: Using requests_html for {url_str}")
        scraper_output = _scrape_with_requests_html(url_str, job_id)
    else:
        logger.error(
            f"Invalid SCRAPER_MODE: {settings.SCRAPER_MODE}. Defaulting to requests_html."
        )
        scraper_output = _scrape_with_requests_html(url_str, job_id)

    if (
        not scraper_output
    ):  # Should be an instance of ScraperOutput from requests_html at least
        logger.error(
            f"Scraping failed completely for URL: {url_str}. Returning default empty output."
        )
        return ScraperOutput(
            html="",
            sample=[],
            image_sources=[],
            major_sections=[],
            screenshot_bytes=b"",
            original_url=AnyHttpUrl(url_str),
        )

    if scraper_output.html is None:  # Should not happen if Pydantic model has defaults
        logger.warning(
            f"Scraper output for {url_str} had None for HTML. Defaulting to empty string."
        )
        scraper_output.html = ""
    if not scraper_output.screenshot_bytes:
        logger.warning(
            f"Scraper output for {url_str} is missing screenshot bytes. Proceeding without visual data."
        )

    logger.info(
        f"Scraping completed for URL: {url_str}. HTML length: {len(scraper_output.html)}, Screenshot bytes: {len(scraper_output.screenshot_bytes)}"
    )
    return scraper_output


if __name__ == "__main__":
    import asyncio

    async def main_test():
        test_url = "https://example.com"
        # To test local playwright:
        # settings.SCRAPER_MODE = ScraperModeEnum.LOCAL_PLAYWRIGHT
        # To test auto with Browserbase (ensure BROWSERBASE_KEY and BROWSERBASE_PROJECT_ID are in .env):
        # settings.SCRAPER_MODE = ScraperModeEnum.AUTO
        # To test HTML only:
        # settings.SCRAPER_MODE = ScraperModeEnum.HTML_ONLY

        if settings.SCRAPER_MODE == ScraperModeEnum.AUTO and not (
            settings.BROWSERBASE_KEY and settings.BROWSERBASE_PROJECT_ID
        ):
            logger.warning(
                "AUTO mode selected but Browserbase keys not found. Consider LOCAL_PLAYWRIGHT or HTML_ONLY, or set keys."
            )
            # Forcing a testable mode if Browserbase isn't set up for AUTO
            # settings.SCRAPER_MODE = ScraperModeEnum.LOCAL_PLAYWRIGHT
            # logger.info(f"Forcing mode to {settings.SCRAPER_MODE.value} for test as Browserbase keys missing.")

        logger.info(
            f"Testing scrape function with URL: {test_url}, Mode: {settings.SCRAPER_MODE.value}"
        )
        start_time = time.time()
        output = await scrape(url_str=test_url, job_id="test_job_local_001")
        end_time = time.time()
        logger.info(f"Scrape function finished in {end_time - start_time:.2f} seconds.")

        if output:
            logger.info(f"Original URL: {output.original_url}")
            logger.info(
                f"HTML content length: {len(output.html or '')}"
            )  # Handle potential None from bad scrape
            logger.info(f"Sample data (first 5 items): {output.sample[:5]}")
            logger.info(f"Image sources: {output.image_sources}")
            logger.info(
                f"Screenshot bytes length: {len(output.screenshot_bytes or b'')}"
            )
            if output.screenshot_bytes:
                screenshot_path = os.path.join(
                    settings.TEMP_DIR, "test_job_local_001", "test_screenshot.png"
                )
                os.makedirs(os.path.dirname(screenshot_path), exist_ok=True)
                with open(screenshot_path, "wb") as f:
                    f.write(output.screenshot_bytes)
                logger.info(f"Test screenshot saved to: {screenshot_path}")
            if output.html:
                html_path = os.path.join(
                    settings.TEMP_DIR, "test_job_local_001", "test_page.html"
                )
                os.makedirs(os.path.dirname(html_path), exist_ok=True)
                with open(html_path, "w", encoding="utf-8") as f:
                    f.write(output.html)
                logger.info(f"Test HTML saved to: {html_path}")
        else:
            logger.error("Scrape function returned None or empty output.")

    if sys.platform == "win32":
        asyncio.set_event_loop_policy(asyncio.WindowsSelectorEventLoopPolicy())
    asyncio.run(main_test())
