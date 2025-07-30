import os
from enum import Enum
from typing import Optional

from pydantic import Field
from pydantic_settings import BaseSettings, SettingsConfigDict


class ScraperModeEnum(str, Enum):
    AUTO = "auto"
    HTML_ONLY = "html_only"
    LOCAL_PLAYWRIGHT = "local_playwright"  # Added new mode


class ModelProviderEnum(str, Enum):
    CLAUDE = "CLAUDE"
    GPT4O = "GPT4O"
    GEMINI = "GEMINI"
    # PHI3 is used internally via Ollama, not configured as a primary MODEL choice here
    # as it's for drafting. The MODEL env var is for the refinement model.


class Settings(BaseSettings):
    model_config = SettingsConfigDict(
        env_file=".env", env_file_encoding="utf-8", extra="ignore"
    )

    # Redis
    REDIS_URL: str = Field("redis://redis:6379/0", validation_alias="REDIS_URL")

    # MinIO (S3-compatible storage)
    AWS_ENDPOINT_URL: Optional[str] = Field(
        "http://minio:9000", validation_alias="AWS_ENDPOINT_URL"
    )
    AWS_ACCESS_KEY_ID: str = Field("minioadmin", validation_alias="AWS_ACCESS_KEY_ID")
    AWS_SECRET_ACCESS_KEY: str = Field(
        "minioadmin", validation_alias="AWS_SECRET_ACCESS_KEY"
    )
    AWS_DEFAULT_REGION: str = Field(
        "us-east-1", validation_alias="AWS_DEFAULT_REGION"
    )  # Required by boto3
    MINIO_BUCKET_NAME: str = "artifacts"
    MINIO_PUBLIC_ENDPOINT_URL: Optional[str] = Field(
        "http://localhost:9000", validation_alias="MINIO_PUBLIC_ENDPOINT_URL"
    )  # For generating browser-accessible pre-signed URLs

    # LLM and Scraper API Keys
    ANTHROPIC_KEY: Optional[str] = Field(None, validation_alias="ANTHROPIC_KEY")
    BROWSERBASE_KEY: Optional[str] = Field(None, validation_alias="BROWSERBASE_KEY")
    BROWSERBASE_PROJECT_ID: Optional[str] = Field(
        None, validation_alias="BROWSERBASE_PROJECT_ID"
    )
    OPENAI_API_KEY: Optional[str] = Field(None, validation_alias="OPENAI_API_KEY")
    GOOGLE_API_KEY: Optional[str] = Field(None, validation_alias="GOOGLE_API_KEY")

    # Model Configuration
    MODEL: ModelProviderEnum = Field(ModelProviderEnum.GEMINI, validation_alias="MODEL")
    GEMINI_MAX_OUTPUT_TOKENS_DESCRIPTION: int = Field(
        16384,
        validation_alias="GEMINI_MAX_OUTPUT_TOKENS_DESCRIPTION",
        description="Max output tokens for Gemini when generating image descriptions.",
    )
    # Fallback logic is handled in orchestrator.py based on available keys if primary fails

    # Scraper Configuration
    SCRAPER_MODE: ScraperModeEnum = Field(
        ScraperModeEnum.AUTO, validation_alias="SCRAPER_MODE"
    )

    # Job Queue
    CLONE_QUEUE_NAME: str = "clone-queue"

    # Temporary file storage path (within the container)
    TEMP_DIR: str = "/tmp/hello"

    # Target SSIM for refinement loop
    TARGET_SSIM: float = 0.92
    MAX_REFINEMENT_ATTEMPTS: int = Field(5, validation_alias="MAX_REFINEMENT_ATTEMPTS")

    # Browserbase API endpoint
    BROWSERBASE_API_URL: str = (
        "https://api.browserbase.com/v1"  # Standard Browserbase API endpoint
    )

    # Ensure temp dir exists
    def __init__(self, **values):
        super().__init__(**values)
        os.makedirs(self.TEMP_DIR, exist_ok=True)


# Instantiate settings to be imported by other modules
settings = Settings()

# Example of how to access a setting:
# from app.settings import settings
# print(settings.REDIS_URL)
