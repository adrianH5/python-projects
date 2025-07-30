from typing import List, Optional, Any, Dict

from pydantic import AnyHttpUrl, BaseModel, Field


class ScraperOutput(BaseModel):
    html: str
    # Sample: List of dicts, each with tagName and computed CSS properties
    sample: List[Dict[str, Any]]
    image_sources: List[str] = Field(
        default_factory=list,
        description="List of absolute URLs for images found on the page.",
    )
    major_sections: List[Dict[str, Any]] = Field(
        default_factory=list,
        description="List of identified major page sections with their details.",
    )
    screenshot_bytes: bytes  # PNG screenshot as bytes
    original_url: AnyHttpUrl


class MerkleNode(BaseModel):
    id: str  # Hash of the node
    tag: str
    attrs: dict[str, str]
    children_ids: List[str]
    # For WL hashing, we might store the WL hash history or final WL hash here too
    wl_hash: str


class MerkleDag(BaseModel):
    # Stores unique components by their final WL hash or Merkle hash
    # Key: component_hash (final WL hash), Value: MerkleNode
    components: dict[str, MerkleNode]
    # Root node(s) of the DAG, could be a list of top-level element hashes
    # For simplicity, we can just store all components and reconstruct hierarchy
    # Or, define a root_id if there's a single conceptual root (e.g. <html> hash)
    root_hashes: List[str]


class DesignTokens(BaseModel):
    colors: List[str]  # Hex color codes
    fonts: List[str]  # Font sizes (e.g., "16px")
    spacing: List[str]  # Margin/padding values (e.g., "8px")


class LLMPromptPack(BaseModel):
    original_url: AnyHttpUrl
    # Merkle DAG might be too complex for direct LLM input,
    # so we'd send a compressed/summarized version.
    # The spec mentions "compress_pack(tokens, components, dag, bundle["screenshot"])"
    # Let's assume 'components' is a simplified list derived from the DAG.
    components_summary: str  # A textual summary or simplified structure of components
    design_tokens: DesignTokens
    # Screenshot might be passed as a data URL or a reference if the LLM supports it.
    # For Phi-3 locally, it might be a path or base64 string.
    # For Claude, it might be a base64 string.
    # The prompt pack is for Phi-3, which might not handle images directly in all Ollama setups.
    # The refinement loop sends heatmap PNG to Claude, which does handle images.
    # Let's assume screenshot_base64 is for Claude, and Phi-3 gets a description or nothing.
    target_html_structure_suggestion: Optional[str] = (
        None  # Optional, from initial analysis
    )


class RefinementPayload(BaseModel):
    original_screenshot_base64: str  # Base64 encoded PNG of original site
    current_html_draft: str
    heatmap_base64: Optional[str] = None  # Base64 encoded PNG of diff heatmap
    previous_critique: Optional[str] = None
    target_ssim: float
    current_ssim: float
    original_url: AnyHttpUrl
    # Include relevant parts of LLMPromptPack if needed for context
    components_summary: str
    design_tokens: DesignTokens
