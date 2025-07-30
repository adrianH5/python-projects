import logging
import boto3
from botocore.exceptions import NoCredentialsError, PartialCredentialsError, ClientError
from typing import Optional, List, Dict, Any

from app.core.config import settings

logger = logging.getLogger(__name__)

# Initialize S3 client
try:
    s3_client = boto3.client(
        "s3",
        endpoint_url=settings.AWS_ENDPOINT_URL,
        aws_access_key_id=settings.AWS_ACCESS_KEY_ID,
        aws_secret_access_key=settings.AWS_SECRET_ACCESS_KEY,
        region_name=settings.AWS_DEFAULT_REGION,  # Boto3 requires a region
    )
except (NoCredentialsError, PartialCredentialsError) as e:
    logger.error(f"Credentials not available for S3 client: {e}")
    s3_client = None
except Exception as e:
    logger.error(f"Error initializing S3 client: {e}")
    s3_client = None


def ensure_bucket_exists(bucket_name: str):
    """
    Ensures that the specified S3 bucket exists, creating it if necessary.
    """
    if not s3_client:
        logger.error("S3 client not initialized. Cannot ensure bucket exists.")
        return False
    try:
        s3_client.head_bucket(Bucket=bucket_name)
        logger.info(f"Bucket '{bucket_name}' already exists.")
    except ClientError as e:
        error_code = e.response.get("Error", {}).get("Code")
        if error_code == "404" or error_code == "NoSuchBucket":
            logger.info(f"Bucket '{bucket_name}' does not exist. Creating it...")
            try:
                if (
                    settings.AWS_ENDPOINT_URL
                    and "amazonaws.com" not in settings.AWS_ENDPOINT_URL
                ):
                    s3_client.create_bucket(Bucket=bucket_name)
                else:
                    if settings.AWS_DEFAULT_REGION == "us-east-1":
                        s3_client.create_bucket(Bucket=bucket_name)
                    else:
                        s3_client.create_bucket(
                            Bucket=bucket_name,
                            CreateBucketConfiguration={
                                "LocationConstraint": settings.AWS_DEFAULT_REGION
                            },
                        )
                logger.info(f"Bucket '{bucket_name}' created successfully.")
            except ClientError as ce:
                logger.error(f"Error creating bucket '{bucket_name}': {ce}")
                return False
        else:
            logger.error(f"Error checking bucket '{bucket_name}': {e}")
            return False
    return True


if settings.MINIO_BUCKET_NAME:
    ensure_bucket_exists(settings.MINIO_BUCKET_NAME)


def minio_put_object(
    key: str, data: bytes, content_type: Optional[str] = None
) -> Optional[str]:
    if not s3_client:
        logger.error("S3 client not initialized. Cannot put object.")
        return None

    bucket_name = settings.MINIO_BUCKET_NAME
    if not ensure_bucket_exists(bucket_name):
        logger.error(f"Bucket '{bucket_name}' does not exist and could not be created.")
        return None

    try:
        extra_args = {}
        if content_type:
            extra_args["ContentType"] = content_type

        s3_client.put_object(Bucket=bucket_name, Key=key, Body=data, **extra_args)
        logger.info(f"Successfully uploaded '{key}' to bucket '{bucket_name}'.")

        presigned_url = s3_client.generate_presigned_url(
            "get_object",
            Params={"Bucket": bucket_name, "Key": key},
            ExpiresIn=900,
        )
        logger.info(f"Generated internal pre-signed URL for '{key}': {presigned_url}")

        if (
            settings.AWS_ENDPOINT_URL
            and settings.MINIO_PUBLIC_ENDPOINT_URL
            and settings.AWS_ENDPOINT_URL in presigned_url
        ):
            public_presigned_url = presigned_url.replace(
                settings.AWS_ENDPOINT_URL, settings.MINIO_PUBLIC_ENDPOINT_URL
            )
            logger.info(
                f"Returning public pre-signed URL for '{key}': {public_presigned_url}"
            )
            return public_presigned_url

        logger.info(
            f"Returning original pre-signed URL for '{key}' (no replacement needed or configured): {presigned_url}"
        )
        return presigned_url
    except ClientError as e:
        logger.error(f"Error uploading '{key}' to bucket '{bucket_name}': {e}")
    except Exception as e:
        logger.error(f"An unexpected error occurred during S3 upload for '{key}': {e}")
    return None


def get_presigned_url(key: str, expires_in: int = 900) -> Optional[str]:
    if not s3_client:
        logger.error("S3 client not initialized. Cannot get pre-signed URL.")
        return None

    bucket_name = settings.MINIO_BUCKET_NAME
    try:
        presigned_url = s3_client.generate_presigned_url(
            "get_object",
            Params={"Bucket": bucket_name, "Key": key},
            ExpiresIn=expires_in,
        )
        logger.info(f"Generated internal pre-signed URL for '{key}': {presigned_url}")

        if (
            settings.AWS_ENDPOINT_URL
            and settings.MINIO_PUBLIC_ENDPOINT_URL
            and settings.AWS_ENDPOINT_URL in presigned_url
        ):
            public_presigned_url = presigned_url.replace(
                settings.AWS_ENDPOINT_URL, settings.MINIO_PUBLIC_ENDPOINT_URL
            )
            logger.info(
                f"Returning public pre-signed URL for '{key}': {public_presigned_url}"
            )
            return public_presigned_url

        logger.info(
            f"Returning original pre-signed URL for '{key}' (no replacement needed or configured): {presigned_url}"
        )
        return presigned_url
    except ClientError as e:
        logger.error(
            f"Error generating pre-signed URL for '{key}' in bucket '{bucket_name}': {e}"
        )
    except Exception as e:
        logger.error(
            f"An unexpected error occurred generating pre-signed URL for '{key}': {e}"
        )
    return None


def list_liquid_artifacts(max_items: int = 50) -> List[Dict[str, Any]]:
    """
    Lists Liquid artifacts from the MinIO bucket and generates pre-signed URLs.

    Args:
        max_items: Maximum number of items to return.

    Returns:
        A list of dictionaries, each containing 'key', 'url', and 'last_modified'.
    """
    if not s3_client:
        logger.error("S3 client not initialized. Cannot list artifacts.")
        return []

    bucket_name = settings.MINIO_BUCKET_NAME
    artifacts = []
    try:
        response = s3_client.list_objects_v2(
            Bucket=bucket_name, MaxKeys=1000
        )  # Fetch more initially if filtering
        all_objects = response.get("Contents", [])

        # Sort by LastModified date in descending order
        all_objects.sort(key=lambda x: x.get("LastModified"), reverse=True)

        for obj in all_objects:
            key = obj.get("Key")
            if key and key.endswith(".liquid"):
                url = get_presigned_url(key)
                if url:
                    artifacts.append(
                        {
                            "key": key,
                            "url": url,
                            "last_modified": (
                                obj.get("LastModified").isoformat()
                                if obj.get("LastModified")
                                else None
                            ),
                            "size": obj.get("Size"),
                        }
                    )
                else:
                    logger.warning(
                        f"Failed to generate pre-signed URL for Liquid artifact: {key}"
                    )
                if len(artifacts) >= max_items:
                    break
        logger.info(
            f"Found {len(artifacts)} Liquid artifacts in bucket '{bucket_name}'."
        )
    except ClientError as e:
        logger.error(f"Error listing objects in bucket '{bucket_name}': {e}")
    except Exception as e:
        logger.error(f"An unexpected error occurred listing Liquid artifacts: {e}")
    return artifacts


if __name__ == "__main__":
    logging.basicConfig(level=logging.INFO)
    logger.info("Testing S3 storage functions...")

    if not s3_client:
        logger.error("S3 client failed to initialize. Aborting test.")
    else:
        test_bucket = settings.MINIO_BUCKET_NAME
        logger.info(f"Using bucket: {test_bucket}")

        if ensure_bucket_exists(test_bucket):
            logger.info(f"Bucket '{test_bucket}' is ready.")

            test_key = "test_file.txt"
            test_data = b"Hello from  S3 storage test!"
            url = minio_put_object(test_key, test_data, content_type="text/plain")

            if url:
                logger.info(f"File uploaded. Access it (for 15 mins) at: {url}")
                import requests

                try:
                    response = requests.get(url)
                    response.raise_for_status()
                    logger.info(f"Successfully fetched back content: {response.text}")
                except requests.RequestException as e:
                    logger.error(f"Failed to fetch from presigned URL: {e}")
            else:
                logger.error("Failed to upload file and get pre-signed URL.")

            existing_url = get_presigned_url(test_key)
            if existing_url:
                logger.info(
                    f"Pre-signed URL for existing object '{test_key}': {existing_url}"
                )
            else:
                logger.error(
                    f"Failed to get pre-signed URL for existing object '{test_key}'."
                )

            # Test listing Liquid artifacts
            logger.info("Testing list_liquid_artifacts...")
            # Create some dummy Liquid files for testing
            minio_put_object(
                "dummy1.liquid",
                b"<html><body>{{ product.title }}</body></html>",
                "text/plain",
            )
            minio_put_object(
                "job1/dummy2.liquid",
                b"<html><body>{% for product in collection.products %}...{% endfor %}</body></html>",
                "text/plain",
            )
            minio_put_object("another.txt", b"some text", "text/plain")

            liquid_files = list_liquid_artifacts()
            if liquid_files:
                logger.info(f"Found {len(liquid_files)} Liquid files:")
                for f_info in liquid_files:
                    logger.info(
                        f"  - Key: {f_info['key']}, URL: {f_info['url']}, LastModified: {f_info['last_modified']}, Size: {f_info['size']}"
                    )
            else:
                logger.info("No Liquid files found or error listing them.")
        else:
            logger.error(
                f"Failed to ensure bucket '{test_bucket}' exists. Test aborted."
            )
