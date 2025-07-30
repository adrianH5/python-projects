from enum import Enum
from typing import Optional

from pydantic import AnyHttpUrl, BaseModel, Field, HttpUrl


class JobStatus(str, Enum):
    PENDING = "pending"
    IN_PROGRESS = "in_progress"
    DONE = "done"
    ERROR = "error"


class StatusResponse(BaseModel):
    job_id: str = Field(..., description="The unique identifier for the cloning job.")
    state: JobStatus = Field(..., description="The current state of the cloning job.")
    message: Optional[str] = Field(
        None, description="An optional message, typically used for errors."
    )
    original_url: Optional[AnyHttpUrl] = Field(
        None, description="The original URL that was requested for cloning."
    )
    artifact_url: Optional[HttpUrl] = Field(
        None, description="The URL to the cloned Liquid artifact in MinIO."
    )
    screenshot_url: Optional[HttpUrl] = Field(
        None, description="The URL to the original screenshot artifact in MinIO."
    )
    cloned_screenshot_url: Optional[HttpUrl] = Field(
        None, description="The URL to the cloned page screenshot artifact in MinIO."
    )
    diff_heatmap_url: Optional[HttpUrl] = Field(
        None, description="The URL to the diff heatmap image artifact in MinIO."
    )
    ssim: Optional[float] = Field(
        None,
        description="Structural Similarity Index (SSIM) between original and clone.",
    )
    attempts: Optional[int] = Field(
        None, description="Number of refinement attempts made by the LLM."
    )
    timestamp: Optional[str] = Field(
        None, description="Timestamp of the last status update."
    )
