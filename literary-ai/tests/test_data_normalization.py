from scripts.data_normalization import normalize_text


def test_normalize_text():
    raw_text = "This    is   a  sample.\n\nPage  1\nWeird spacing \n"
    norm = normalize_text(raw_text)
    # Check that extra whitespace is removed, newlines are replaced
    assert "Page 1" not in norm
    assert "Weird spacing" in norm
    # Confirm it’s a single line or minimal lines
    assert "  " not in norm  # no double spaces
    assert norm.strip().startswith("This is a sample.")
