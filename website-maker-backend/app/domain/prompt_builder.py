import json
from pathlib import Path
from typing import Dict, Any, Optional

PROMPTS_DIR = Path(__file__).parent / "prompts"


def get_image_description_prompt() -> str:
    """Reads and returns the static prompt for generating an image description."""
    with open(PROMPTS_DIR / "image_description.txt", "r", encoding="utf-8") as f:
        return f.read()


def _format_major_sections(major_sections: list) -> str:
    """Formats the major sections data into a readable string."""
    if not major_sections:
        return "  (No specific major sections identified by scraper)"

    formatted_sections = []
    for s in major_sections:
        tag_info = f"<{s.get('tagName', 'div')}"
        if s.get("id"):
            tag_info += f" id='{s.get('id')}'"
        if s.get("classList"):
            tag_info += f" class='{' '.join(s.get('classList'))}'"
        tag_info += ">"

        details = (
            f"(contains approx. {s.get('childElementCount', 0)} child elements; "
            f"text hint: \"{s.get('textContentSnippet', '')}\")"
        )
        formatted_sections.append(f"  - Section: {tag_info} {details}")
    return "\n".join(formatted_sections)


def get_initial_draft_prompt(
    prompt_pack: Dict[str, Any], image_description: Optional[str]
) -> str:
    """Builds the prompt for generating the initial Liquid draft from a template file."""
    asset_mapping = prompt_pack.get("asset_mapping", {})
    tokens_data = prompt_pack.get("design_tokens", {})

    if image_description:
        image_description_section = (
            "\n--- Primary Task & Data (MOST IMPORTANT) ---\n"
            "Your primary guide is the following detailed textual description of the webpage. **Incorporate every detail from this description. It is the source of truth for all structure, text, and styling.**\n"
            "--- TEXTUAL DESCRIPTION START ---\n"
            f"{image_description}\n"
            "--- TEXTUAL DESCRIPTION END ---\n\n"
            "Use the description for structure, layout, and content. The original screenshot is also provided as a visual reference.\n"
            "**CRITICAL**: The 'DESIGN TOKENS' and other scraped data below are for reference only. **If they conflict with the TEXTUAL DESCRIPTION, the TEXTUAL DESCRIPTION takes precedence.**"
        )
    else:
        image_description_section = (
            "\n--- Primary Task & Data ---\n"
            "Base your Liquid code on the provided screenshot and the detailed scraped data below.\n"
            "The screenshot is your primary visual guide. **You must replicate everything visible.**\n"
            "**CRITICAL**: The 'DESIGN TOKENS' section provides the EXACT styling values (font weights, colors, spacing, etc.) you MUST implement using Tailwind CSS and CSS variables."
        )

    with open(PROMPTS_DIR / "initial_draft.txt", "r", encoding="utf-8") as f:
        template = f.read()

    # Use str.replace instead of str.format to avoid conflicts with Liquid syntax
    template = template.replace(
        "{image_description_section}", image_description_section
    )
    template = template.replace(
        "{original_url}", prompt_pack.get("original_url", "N/A")
    )
    template = template.replace("{asset_mapping}", json.dumps(asset_mapping, indent=2))
    template = template.replace("{colors}", str(tokens_data.get("colors", [])))
    template = template.replace("{fonts}", str(tokens_data.get("fonts", [])))
    template = template.replace("{spacing}", str(tokens_data.get("spacing", [])))
    template = template.replace(
        "{components_summary}", prompt_pack.get("components_summary", "N/A")
    )
    template = template.replace(
        "{major_sections}",
        _format_major_sections(prompt_pack.get("major_sections", [])),
    )

    return template


def get_refinement_prompt(pack: Dict[str, Any], critique: str) -> str:
    """Builds the prompt for refining an existing Liquid draft from a template file."""
    with open(PROMPTS_DIR / "refinement.txt", "r", encoding="utf-8") as f:
        template = f.read()

    # Use str.replace instead of str.format to avoid conflicts with Liquid syntax
    template = template.replace("{original_url}", pack.get("original_url", "N/A"))
    template = template.replace("{critique}", critique)
    template = template.replace(
        "{colors}", str(pack.get("design_tokens", {}).get("colors", []))
    )
    template = template.replace(
        "{fonts}", str(pack.get("design_tokens", {}).get("fonts", []))
    )
    template = template.replace(
        "{spacing}", str(pack.get("design_tokens", {}).get("spacing", []))
    )
    template = template.replace(
        "{components_summary}", pack.get("components_summary", "N/A")
    )
    template = template.replace(
        "{major_sections}", _format_major_sections(pack.get("major_sections", []))
    )
    template = template.replace(
        "{asset_mapping}", json.dumps(pack.get("asset_mapping", {}), indent=2)
    )

    return template
