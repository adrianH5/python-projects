import datetime
from typing import List, Optional

from pydantic import AnyHttpUrl, BaseModel, Field


class CloneRequest(BaseModel):
    url: AnyHttpUrl = Field(..., description="The URL of the website to clone.")
    capture_full_page: bool = Field(
        True,
        description="Whether to attempt a full-page scrolling screenshot. Defaults to True.",
    )


class CloneResponse(BaseModel):
    job_id: str = Field(..., description="The unique identifier for the cloning job.")


class LiquidArtifact(BaseModel):
    key: str
    url: AnyHttpUrl
    last_modified: Optional[datetime.datetime] = None
    size: Optional[int] = None


class CloneHistoryResponse(BaseModel):
    artifacts: List[LiquidArtifact]
    count: int
