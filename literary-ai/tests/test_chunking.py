from scripts.chunking import chunk_text


def test_chunk_text():
    text = " ".join(["word" + str(i) for i in range(1200)])
    chunks = chunk_text(text, chunk_size=500)
    assert len(chunks) == 3
    # Check chunk sizes
    assert len(chunks[0].split()) == 500
    assert len(chunks[1].split()) == 500
    assert len(chunks[2].split()) == 200
