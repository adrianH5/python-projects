1. **Custom Tokenization** - WordPiece implementation comparing legal vs literary texts
2. **Word Embeddings** - CBOW and Skip-gram models for legal text analysis
3. **Audio Processing** - Speech-to-text transcription pipeline
4. **Formal Verification I** - SMT modeling of legal dependency rules
5. **Formal Verification II** - Extended SMT modeling with scenario validation
6. **Term Project** - Fine-tuning LLMs for US tax dependency classification

### Project 1: WordPiece Tokenization

- Implemented WordPiece tokenizer from scratch
- Analyzed subword tokenization differences between legal and literary texts
- Legal text: 31,332 tokens (3,172 unique)
- Literary text: 51,776 tokens (3,018 unique)
- 590 common tokens, demonstrating domain-specific vocabulary

### Project 2: Word Embeddings

- Built CBOW and Skip-gram models without using pre-built libraries
- Trained on legal corpus to capture domain-specific semantics
- Compared embedding quality between architectures

### Project 3: Audio Processing

- Developed speech-to-text pipeline for legal audio content
- Processed audio files and generated accurate transcriptions

### Project 4 & 5: Formal Verification

- Modeled US tax dependency rules (26 USC 152) using SMT-LIB
- Created comprehensive test scenarios for dependent/non-dependent cases
- Validated legal logic through formal methods
- Key SMT features:
  - Relationship modeling (parent, child, sibling, etc.)
  - Support calculations (>50% rule)
  - Residency requirements
  - Income thresholds

### Term Project: LLM Fine-tuning

- **Model**: Microsoft Phi-3-mini-4k-instruct
- **Method**: LoRA fine-tuning with 4-bit quantization
- **Dataset**: 384 custom examples of tax dependency scenarios
- **Configuration**:
  - LoRA rank: 16, alpha: 32, dropout: 0.05
  - Target modules: ['down_proj', 'gate_up_proj', 'o_proj', 'qkv_proj']
  - 100 epochs, batch size 4, gradient accumulation 8
  - Learning rate: 2e-4 with cosine scheduler
- **Results**: Successfully classifies complex dependency scenarios

