import logging

from fastapi import HTTPException

from app.schemas.clone import LiquidArtifact, CloneHistoryResponse
from app.services.storage import get_presigned_url, list_liquid_artifacts

logger = logging.getLogger(__name__)


def get_artifact_url(object_key: str):
    """Generates a presigned URL for a given MinIO object key."""
    presigned_url = get_presigned_url(key=object_key, expires_in=900)

    if not presigned_url:
        logger.error(
            f"Could not generate pre-signed URL for artifact with key: {object_key}"
        )
        raise HTTPException(
            status_code=404,
            detail=f"Artifact with key '{object_key}' not found or URL generation failed.",
        )
    return {"url": presigned_url, "expires_in_seconds": 900}


def get_clone_history(limit: int) -> CloneHistoryResponse:
    """
    Retrieves a list of previously cloned Liquid artifacts from MinIO.
    """
    try:
        artifacts_data = list_liquid_artifacts(max_items=limit)
        liquid_artifacts = [LiquidArtifact(**data) for data in artifacts_data]
        return CloneHistoryResponse(
            artifacts=liquid_artifacts, count=len(liquid_artifacts)
        )
    except Exception as e:
        logger.error(f"Error retrieving clone history: {e}", exc_info=True)
        raise HTTPException(
            status_code=500, detail="Internal server error retrieving clone history."
        )
