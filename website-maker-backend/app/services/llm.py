import logging
import re
from typing import Optional, Dict, Any

import httpx
from app.core.config import settings, ModelProviderEnum
from app.core.constants import (
    LLM_API_TIMEOUT,
    LLM_HTML_API_TIMEOUT,
    LLM_DESCRIPTION_MAX_TOKENS,
    LLM_HTML_MAX_TOKENS,
    GEMINI_HTML_MAX_OUTPUT_TOKENS,
)

logger = logging.getLogger(__name__)


def get_effective_model_provider(
    job_id: str, requested_provider: ModelProviderEnum
) -> Optional[ModelProviderEnum]:
    """Determines which model to use based on available API keys, with fallbacks."""
    provider_keys = {
        ModelProviderEnum.GEMINI: settings.GOOGLE_API_KEY,
        ModelProviderEnum.CLAUDE: settings.ANTHROPIC_KEY,
        ModelProviderEnum.GPT4O: settings.OPENAI_API_KEY,
    }
    # Define a fallback order
    fallback_order = [
        ModelProviderEnum.CLAUDE,
        ModelProviderEnum.GEMINI,
        ModelProviderEnum.GPT4O,
    ]

    if provider_keys.get(requested_provider):
        return requested_provider

    logger.warning(
        f"Job {job_id}: Key for requested provider '{requested_provider.value}' not found. Attempting fallbacks."
    )

    for provider in fallback_order:
        if provider != requested_provider and provider_keys.get(provider):
            logger.info(f"Job {job_id}: Falling back to '{provider.value}'.")
            return provider

    logger.error(f"Job {job_id}: No API keys found for any supported model provider.")
    return None


def _prepare_api_request(
    job_id: str, model_provider: ModelProviderEnum, content: list, max_tokens: int
) -> Optional[Dict[str, Any]]:
    """Prepares the API key, URL, headers, and payload for a given model provider."""
    api_key, api_url = None, ""
    headers, payload = {}, {}

    if model_provider == ModelProviderEnum.CLAUDE:
        api_key, api_url = (
            settings.ANTHROPIC_KEY,
            "https://api.anthropic.com/v1/messages",
        )
        model_name = (
            "claude-3-sonnet-20240229"
            if "sonnet" in settings.MODEL.value
            else "claude-3-opus-20240229"
        )
        payload = {"model": model_name, "max_tokens": max_tokens, "messages": content}
        headers = {
            "x-api-key": api_key,
            "anthropic-version": "2023-06-01",
            "content-type": "application/json",
        }

    elif model_provider == ModelProviderEnum.GPT4O:
        api_key, api_url = (
            settings.OPENAI_API_KEY,
            "https://api.openai.com/v1/chat/completions",
        )
        payload = {"model": "gpt-4o", "messages": content, "max_tokens": max_tokens}
        headers = {
            "Authorization": f"Bearer {api_key}",
            "Content-Type": "application/json",
        }

    elif model_provider == ModelProviderEnum.GEMINI:
        api_key = settings.GOOGLE_API_KEY
        api_url = f"https://generativelanguage.googleapis.com/v1beta/models/gemini-2.5-pro-preview-05-06:generateContent?key={api_key}"
        payload = {
            "contents": content,
            "generationConfig": {
                "maxOutputTokens": max_tokens,
                "responseMimeType": "text/plain",
            },
        }
        headers = {"Content-Type": "application/json"}

    if not api_key:
        logger.error(f"Job {job_id}: API key for {model_provider.value} is not set.")
        return None

    return {"url": api_url, "headers": headers, "payload": payload}


def _parse_llm_response(
    job_id: str, model_provider: ModelProviderEnum, api_data: Dict[str, Any]
) -> str:
    """Parses the generated text from an LLM API response."""
    try:
        if model_provider == ModelProviderEnum.CLAUDE:
            return api_data["content"][0].get("text", "").strip()
        elif model_provider == ModelProviderEnum.GPT4O:
            return api_data["choices"][0].get("message", {}).get("content", "").strip()
        elif model_provider == ModelProviderEnum.GEMINI:
            return (
                api_data["candidates"][0]["content"]["parts"][0].get("text", "").strip()
            )
    except (IndexError, KeyError) as e:
        logger.error(
            f"Job {job_id}: Could not extract text from {model_provider.value} response. Error: {e}. Response: {api_data}"
        )
    return ""


def _clean_html_output(job_id: str, raw_html: str) -> str:
    """Cleans the raw HTML output from the LLM, removing markdown code blocks."""
    match = re.search(
        r"```(?:liquid|html)\s*(.*?)\s*```", raw_html, re.DOTALL | re.IGNORECASE
    )
    if match:
        return match.group(1).strip()

    match = re.search(
        r"<(!DOCTYPE html|html).*?>.*?</html\s*>", raw_html, re.DOTALL | re.IGNORECASE
    )
    if match:
        return match.group(0).strip()

    if "```" in raw_html:
        logger.warning(
            f"Job {job_id}: LLM output had no code block/HTML tags. Stripping '```' as a fallback."
        )
        return re.sub(
            r"^```(liquid|html)?\s*|\s*```$", "", raw_html, flags=re.IGNORECASE
        ).strip()

    return raw_html.strip()


async def _execute_llm_call(
    job_id: str,
    model_provider: ModelProviderEnum,
    http_client: httpx.AsyncClient,
    request_params: Dict[str, Any],
    timeout: float,
) -> Optional[Dict[str, Any]]:
    """Executes the HTTP request to the LLM API and handles errors."""
    try:
        response = await http_client.post(
            request_params["url"],
            json=request_params["payload"],
            headers=request_params["headers"],
            timeout=timeout,
        )
        response.raise_for_status()
        return response.json()
    except httpx.HTTPStatusError as e_http:
        error_text = e_http.response.text if e_http.response else "Unknown HTTP error."
        logger.error(
            f"Job {job_id}: {model_provider.value} API HTTP error: {e_http.response.status_code} - {error_text}",
            exc_info=False,
        )
    except Exception as e:
        logger.error(
            f"Job {job_id}: {model_provider.value} API call failed with unexpected error: {e}",
            exc_info=True,
        )
    return None


async def call_for_image_description(
    job_id: str,
    model_provider: ModelProviderEnum,
    prompt_text: str,
    screenshot_b64: str,
    http_client: httpx.AsyncClient,
) -> str:
    """Calls an LLM to generate a textual description of a webpage screenshot."""
    error_response = "Error: Could not generate image description."
    is_gemini = model_provider == ModelProviderEnum.GEMINI

    parts = [{"text": prompt_text}]
    image_part_text = "\n(Above is the screenshot of the website to describe.)\n"
    if is_gemini:
        parts.append(
            {"inline_data": {"mime_type": "image/png", "data": screenshot_b64}}
        )
        parts.append({"text": image_part_text})
    else:
        image_source = {
            "type": "base64",
            "media_type": "image/png",
            "data": screenshot_b64,
        }
        if model_provider == ModelProviderEnum.CLAUDE:
            parts.append({"type": "image", "source": image_source})
        else:  # GPT-4O
            parts.append(
                {
                    "type": "image_url",
                    "image_url": {"url": f"data:image/png;base64,{screenshot_b64}"},
                }
            )
        parts.append({"type": "text", "text": image_part_text})
    parts.append({"text": "Provide the detailed textual description now:"})

    content = (
        [{"role": "user", "parts": parts}]
        if is_gemini
        else [{"role": "user", "content": parts}]
    )

    request_params = _prepare_api_request(
        job_id, model_provider, content, LLM_DESCRIPTION_MAX_TOKENS
    )
    if not request_params:
        return error_response

    logger.info(
        f"Job {job_id}: Sending request to {model_provider.value} for image description."
    )
    api_data = await _execute_llm_call(
        job_id, model_provider, http_client, request_params, LLM_API_TIMEOUT
    )

    if api_data:
        generated_text = _parse_llm_response(job_id, model_provider, api_data)
        if generated_text and "Error:" not in generated_text:
            logger.info(
                f"Job {job_id}: Generated image description from {model_provider.value}. Length: {len(generated_text)}"
            )
            return generated_text
        logger.error(
            f"Job {job_id}: Image description LLM call resulted in empty or error response: '{generated_text}'"
        )

    return error_response


async def call_for_html_generation(
    job_id: str,
    model_provider: ModelProviderEnum,
    prompt_text: str,
    http_client: httpx.AsyncClient,
    is_draft: bool,
    current_html: Optional[str] = None,
    screenshot_b64: Optional[str] = None,
    heatmap_b64: Optional[str] = None,
) -> str:
    """Calls an LLM to generate or refine Liquid HTML code."""
    error_response = (
        current_html
        if not is_draft
        else f"<html><body><p>Error: LLM call failed for job {job_id}.</p></body></html>"
    )

    effective_provider = get_effective_model_provider(job_id, model_provider)
    if not effective_provider:
        return error_response

    is_gemini = effective_provider == ModelProviderEnum.GEMINI
    parts = [{"text": prompt_text}]

    if screenshot_b64:
        image_text = "\n(Above is a screenshot of the *original* target website.)\n"
        if is_gemini:
            parts.append(
                {"inline_data": {"mime_type": "image/png", "data": screenshot_b64}}
            )
            parts.append({"text": image_text})
        else:
            image_source = {
                "type": "base64",
                "media_type": "image/png",
                "data": screenshot_b64,
            }
            if effective_provider == ModelProviderEnum.CLAUDE:
                parts.append({"type": "image", "source": image_source})
            else:  # GPT-4O
                parts.append(
                    {
                        "type": "image_url",
                        "image_url": {"url": f"data:image/png;base64,{screenshot_b64}"},
                    }
                )
            parts.append({"type": "text", "text": image_text})

    if not is_draft and heatmap_b64:
        heatmap_text = (
            "\n(Above is a heatmap showing discrepancies. Red areas need fixing.)\n"
        )
        if is_gemini:
            parts.append(
                {"inline_data": {"mime_type": "image/png", "data": heatmap_b64}}
            )
            parts.append({"text": heatmap_text})
        else:
            heatmap_source = {
                "type": "base64",
                "media_type": "image/png",
                "data": heatmap_b64,
            }
            if effective_provider == ModelProviderEnum.CLAUDE:
                parts.append({"type": "image", "source": heatmap_source})
            else:  # GPT-4O
                parts.append(
                    {
                        "type": "image_url",
                        "image_url": {"url": f"data:image/png;base64,{heatmap_b64}"},
                    }
                )
            parts.append({"type": "text", "text": heatmap_text})

    if not is_draft and current_html:
        parts.append(
            {
                "text": f"\n\nCurrent Liquid draft to refine:\n```liquid\n{current_html}\n```\n"
            }
        )

    final_instruction = (
        "Provide the improved, complete Liquid code now:"
        if not is_draft
        else "Provide the complete Liquid code now:"
    )
    parts.append({"text": final_instruction})

    content = (
        [{"role": "user", "parts": parts}]
        if is_gemini
        else [{"role": "user", "content": parts}]
    )
    max_tokens = GEMINI_HTML_MAX_OUTPUT_TOKENS if is_gemini else LLM_HTML_MAX_TOKENS

    request_params = _prepare_api_request(
        job_id, effective_provider, content, max_tokens
    )
    if not request_params:
        return error_response

    logger.info(
        f"Job {job_id}: Sending request to {effective_provider.value} for {'draft' if is_draft else 'refinement'}."
    )
    api_data = await _execute_llm_call(
        job_id, effective_provider, http_client, request_params, LLM_HTML_API_TIMEOUT
    )

    if api_data:
        generated_html = _parse_llm_response(job_id, effective_provider, api_data)
        cleaned_html = _clean_html_output(job_id, generated_html)
        if cleaned_html:
            logger.info(
                f"Job {job_id}: Processed Liquid from {effective_provider.value}. Length: {len(cleaned_html)}"
            )
            return cleaned_html
        logger.error(f"Job {job_id}: Liquid content empty after cleaning LLM response.")

    return error_response
