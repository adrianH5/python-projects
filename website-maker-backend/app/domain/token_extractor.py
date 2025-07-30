import logging
from collections import Counter
from io import BytesIO
from typing import List, Dict, Union

import numpy as np
from PIL import Image, UnidentifiedImageError
from sklearn.cluster import KMeans
from skimage.color import rgb2lab, lab2rgb


logger = logging.getLogger(__name__)


def extract_palette_from_image(image_input: Union[str, bytes], k: int = 8) -> List[str]:
    """
    Extracts a color palette (k dominant colors) from an image.

    Args:
        image_input: Path to the image file or bytes of the image.
        k: Number of colors to extract.

    Returns:
        A list of k hex color strings.
    """
    try:
        if isinstance(image_input, str):
            img = Image.open(image_input)
        elif isinstance(image_input, bytes):
            if not image_input:
                logger.warning("Empty image bytes received for palette extraction.")
                return []
            img = Image.open(BytesIO(image_input))
        else:
            raise TypeError("image_input must be a path string or bytes.")

        img = img.convert("RGB")  # Ensure image is in RGB format
        img_array = np.array(img)

        # Reshape the image array to be a list of pixels
        pixels = img_array.reshape(-1, 3)

        # Avoid clustering if image is too small or has too few unique colors
        if pixels.shape[0] < k:
            logger.warning(
                f"Image has fewer pixels ({pixels.shape[0]}) than requested clusters ({k}). "
                "Returning unique colors present, padded if necessary."
            )
            unique_colors = np.unique(pixels, axis=0)
            hex_colors = [f"#{r:02x}{g:02x}{b:02x}" for r, g, b in unique_colors[:k]]
            # Pad with a default color (e.g., black) if fewer than k unique colors
            while len(hex_colors) < k and k > 0:  # k > 0 to avoid infinite loop if k=0
                hex_colors.append("#000000")
            return hex_colors[:k]

        # Convert RGB to Lab color space for perceptually uniform clustering
        lab_pixels = rgb2lab(pixels / 255.0)  # skimage expects float0-1 range

        # Perform k-means clustering
        kmeans = KMeans(
            n_clusters=k,
            init="k-means++",  # Smart initialization
            n_init=3,  # Run a few times with different centroids
            max_iter=100,  # Limit iterations
            random_state=42,
            algorithm="lloyd",  # Explicitly set algorithm
        )
        try:
            kmeans.fit(lab_pixels)
        except (
            Exception
        ) as e_kmeans:  # Catch potential errors in KMeans like empty clusters
            logger.error(
                f"KMeans clustering failed: {e_kmeans}. Pixels shape: {lab_pixels.shape}"
            )
            # Fallback: return a default palette or unique colors if few
            default_palette = ["#000000"] * k
            return default_palette

        # Get the cluster centers (dominant colors in Lab)
        dominant_lab_colors = kmeans.cluster_centers_

        # Convert Lab colors back to RGB
        # Ensure Lab values are within typical ranges if necessary, though cluster centers should be fine
        dominant_rgb_colors_float = lab2rgb(
            dominant_lab_colors
        )  # Returns float0-1 range

        # Convert float RGB [0,1] to integer RGB [0,255]
        dominant_rgb_colors_int = (
            np.clip(dominant_rgb_colors_float, 0, 1) * 255
        ).astype(int)

        # Convert RGB to hex
        hex_colors = [f"#{r:02x}{g:02x}{b:02x}" for r, g, b in dominant_rgb_colors_int]

        return hex_colors

    except UnidentifiedImageError:
        logger.error(
            f"Cannot identify image file for palette extraction: {image_input if isinstance(image_input, str) else 'bytes input'}"
        )
    except FileNotFoundError:
        logger.error(f"Image file not found for palette extraction: {image_input}")
    except Exception as e:
        logger.error(f"Error extracting palette: {e}", exc_info=True)

    return ["#000000"] * k  # Fallback: k black colors


def extract_typography_and_spacing(
    sample_data: List[List[str]], top_n: int = 5
) -> Dict[str, List[str]]:
    """
    Extracts typography (font sizes) and spacing (margins, paddings) from sample CSS data.

    Args:
        sample_data: List of lists, where each inner list contains CSS properties.
                     Expected format: [tagName, className, fontSize, margin, padding, color, backgroundColor]
        top_n: Number of top unique values to return for each category.

    Returns:
        A dictionary with "fonts", "margins", and "paddings" lists.
    """
    font_sizes = []
    margins = []
    paddings = []

    # Indices based on scraper.py PLAYWRIGHT_SCRIPT_TEMPLATE output
    # [el.tagName, el.className, cs.fontSize, cs.margin, cs.padding, cs.color, cs.backgroundColor]
    IDX_FONT_SIZE = 2
    IDX_MARGIN = 3
    IDX_PADDING = 4

    for item in sample_data:
        if not isinstance(item, list) or len(item) < IDX_PADDING + 1:
            logger.warning(f"Skipping malformed sample item: {item}")
            continue

        font_size = item[IDX_FONT_SIZE]
        margin = item[IDX_MARGIN]
        padding = item[IDX_PADDING]

        if font_size and isinstance(font_size, str) and font_size.strip():
            font_sizes.append(font_size.strip())
        if margin and isinstance(margin, str) and margin.strip():
            margins.append(margin.strip())
        if padding and isinstance(padding, str) and padding.strip():
            paddings.append(padding.strip())

    # Get top N unique values using Counter
    top_fonts = [val for val, count in Counter(font_sizes).most_common(top_n)]
    top_margins = [val for val, count in Counter(margins).most_common(top_n)]
    top_paddings = [val for val, count in Counter(paddings).most_common(top_n)]

    return {
        "fonts": top_fonts,
        "spacing_margins": top_margins,
        "spacing_paddings": top_paddings,
    }


def extract_tokens(
    image_input: Union[str, bytes], sample_data: List[List[str]]
) -> Dict[str, List[str]]:
    """
    Extracts design tokens (colors, typography, spacing) from a website's
    screenshot and sampled CSS properties.

    Args:
        image_input: Path to the screenshot image file or bytes of the image.
        sample_data: List of lists containing sampled CSS properties from elements.
                     Expected format from scraper:
                     [tagName, className, fontSize, margin, padding, color, backgroundColor]

    Returns:
        A dictionary: {"colors": [...], "fonts": [...], "spacing": [...]}
        As per spec, "spacing" will combine margins and paddings.
        The spec says: "Return dict {colors:[…], fonts:[…], spacing:[…]}"
    """
    logger.info("Starting token extraction...")

    if image_input:
        colors = extract_palette_from_image(image_input, k=8)
    else:
        logger.warning(
            "No image input provided to extract_tokens; color palette will be empty."
        )
        colors = []
    typo_spacing_data = extract_typography_and_spacing(sample_data, top_n=5)

    # Combine margins and paddings for the final "spacing" list,
    # taking unique values and then truncating if necessary, or just concatenating.
    # The spec asks for "spacing:[...]", implying a single list.
    # Let's take top N from combined unique margins and paddings.
    combined_spacing_values = (
        typo_spacing_data["spacing_margins"] + typo_spacing_data["spacing_paddings"]
    )
    top_combined_spacing = [
        val for val, count in Counter(combined_spacing_values).most_common(5)
    ]

    result = {
        "colors": colors,
        "fonts": typo_spacing_data["fonts"],
        "spacing": top_combined_spacing,
    }
    logger.info(
        f"Token extraction completed. Colors: {len(result['colors'])}, Fonts: {len(result['fonts'])}, Spacing: {len(result['spacing'])}"
    )
    return result


if __name__ == "__main__":
    import os

    logging.basicConfig(level=logging.INFO)
    logger.info("Testing token extraction functions...")

    # Create a dummy image for testing if one doesn't exist
    # This is also for the test_tokens.py which expects "tests/assets/stripe.png"
    # For now, let's assume a simple test or that the asset exists.
    # A proper test setup would mock image loading or provide a fixed test image.

    # Test palette extraction
    # Create a simple 10x10 red image for testing
    try:
        dummy_image_array = np.zeros((10, 10, 3), dtype=np.uint8)
        dummy_image_array[:, :, 0] = 255  # Red channel
        dummy_image = Image.fromarray(dummy_image_array)
        img_byte_arr = BytesIO()
        dummy_image.save(img_byte_arr, format="PNG")
        dummy_image_bytes = img_byte_arr.getvalue()

        palette = extract_palette_from_image(dummy_image_bytes, k=3)
        logger.info(
            f"Test palette from dummy red image (k=3): {palette}"
        )  # Expect shades of red or red + black if k > unique

        # Test with a non-existent file
        palette_nonexistent = extract_palette_from_image("nonexistent.png", k=3)
        logger.info(f"Test palette from non-existent file: {palette_nonexistent}")

    except Exception as e:
        logger.error(f"Error in palette test setup: {e}")

    # Test typography and spacing extraction
    sample_css_data = [
        ["P", "text-class", "16px", "8px", "10px 0", "rgb(0,0,0)", "transparent"],
        [
            "DIV",
            "container",
            "14px",
            "16px auto",
            "20px",
            "rgb(50,50,50)",
            "rgb(240,240,240)",
        ],
        ["SPAN", "", "16px", "0", "5px", "blue", "none"],
        ["H1", "title", "32px", "0 0 16px 0", "0", "black", "white"],
        [
            "P",
            "text-class",
            "16px",
            "8px",
            "10px 0",
            "rgb(0,0,0)",
            "transparent",
        ],  # Repeated
        ["A", "link", "14px", "0 4px", "0", "inherit", "transparent"],
        ["DIV", "box", "12px", "5px", "5px", "gray", "lightgray"],
        ["DIV", "box", "12px", "5px", "5px", "gray", "lightgray"],
        ["DIV", "box", "12px", "5px", "5px", "gray", "lightgray"],
        ["DIV", "another", "18px", "10px", "10px", "black", "yellow"],
        [
            "P",
            "special",
            "16px",
            "8px 0 8px 0",
            "12px",
            "red",
            "pink",
        ],  # More complex margin
    ]
    typo_spacing = extract_typography_and_spacing(sample_css_data, top_n=3)
    logger.info(f"Test typography/spacing (top 3): {typo_spacing}")

    # Test combined extract_tokens
    # Assuming dummy_image_bytes is available from above
    if "dummy_image_bytes" in locals():
        all_tokens = extract_tokens(dummy_image_bytes, sample_css_data)
        logger.info(f"Combined extract_tokens output: {all_tokens}")
    else:
        logger.warning(
            "Skipping combined extract_tokens test as dummy image was not created."
        )

    # Test case from spec: extract_tokens(img_path, sample=[])
    # This requires a test asset. Let's simulate an empty sample.
    # And create a dummy asset if needed for the test_tokens.py later.
    test_asset_dir = os.path.join(os.path.dirname(__file__), "..", "tests", "assets")
    os.makedirs(test_asset_dir, exist_ok=True)
    dummy_stripe_path = os.path.join(test_asset_dir, "stripe.png")

    try:
        # Create a simple stripe image (e.g., red and blue stripes)
        stripe_array = np.zeros((60, 100, 3), dtype=np.uint8)
        stripe_array[:, :50, 0] = 255  # Red stripe
        stripe_array[:, 50:, 2] = 255  # Blue stripe
        stripe_image = Image.fromarray(stripe_array)
        stripe_image.save(dummy_stripe_path)
        logger.info(f"Created dummy stripe image at {dummy_stripe_path}")

        tokens_from_stripe_empty_sample = extract_tokens(
            dummy_stripe_path, sample_data=[]
        )
        logger.info(
            f"Tokens from stripe.png with empty sample: {tokens_from_stripe_empty_sample}"
        )
        # Expected: colors should be 8 (might include black/white if image is simple), fonts/spacing empty.
    except Exception as e:
        logger.error(f"Error creating or processing dummy stripe image: {e}")
