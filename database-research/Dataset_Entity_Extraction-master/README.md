# Dataset Entity Extraction

A comprehensive biomedical dataset extraction pipeline that identifies and extracts dataset mentions from PubMed abstracts using GPT-4o and fine-tuned BERT models.

## Overview

This project combines modern NLP techniques to extract dataset mentions from biomedical literature:
- **GPT-4o** for dataset mention detection in abstracts
- **Fine-tuned BioBERT models** for Named Entity Recognition (NER)
- **Relation Extraction (RE)** models for identifying relationships between entities
- **Combined models** for joint NER and RE tasks

## Quick Start

### Installation

```bash
pip install -r requirements.txt
```

### Basic Usage

1. **Extract dataset mentions from PubMed abstracts:**

```bash
python find_datasets.py
```

This will:
- Process all abstracts in `../pubmed_abstracts/`
- Identify dataset mentions using GPT-4o
- Save the 300 longest abstracts containing datasets to `../abstracts_with_datasets_top300/`

2. **Train biomedical NER models:**

```bash
cd Biomedical_datasets/NER/nerbert/
python nerbert.py
```

3. **Train relation extraction models:**

```bash
cd Biomedical_datasets/RE/
python rebert.py
```

## Project Structure

```
Dataset_Entity_Extraction/
├── find_datasets.py              # Main dataset extraction script
├── process_pubmed.py             # PubMed processing utilities
├── requirements.txt              # Python dependencies
├── Biomedical_datasets/
│   ├── NER/                      # Named Entity Recognition
│   │   ├── nerbert/              # BERT-based NER models
│   │   └── data_updated/         # Training data
│   ├── RE/                       # Relation Extraction
│   │   ├── rebert.py             # BERT-based RE models
│   │   └── nospacy_data/         # RE training data
│   ├── combined/                 # Joint NER+RE models
│   ├── data/                     # Biomedical datasets
│   └── extraction_pipeline/      # Processing pipeline
└── llama3/                       # LLM integration
    ├── fine_tune/                # Fine-tuning scripts
    └── test.py                   # Testing utilities
```

## Features

### Dataset Extraction
- **Smart filtering**: Processes ALL abstracts to find dataset mentions, then selects top 300 longest
- **GPT-4o integration**: Uses OpenAI's GPT-4o for accurate dataset identification
- **Incremental processing**: Skips already processed files for efficiency

### Biomedical NER
- **Multiple BioBERT variants**: Supports various pre-trained BioBERT models
- **Custom tokenization**: Handles biomedical terminology with special tokens
- **BIOES tagging**: Uses Begin-Inside-Outside-End-Single entity tagging
- **Configurable training**: Adjustable hyperparameters for different datasets

### Relation Extraction
- **Entity relationships**: Identifies relationships between biomedical entities
- **Joint training**: Can be combined with NER for improved performance
- **Custom loss functions**: Supports weighted loss for imbalanced datasets

## Configuration

### Environment Variables
Create a `.env` file in the project root:
```
OPENAI_API_KEY=your_api_key_here
```

### Model Selection
Edit the model configuration in the respective Python files:
- `nerbert.py`: Change `model_name` variable
- `rebert.py`: Change `model_name` variable

Available models:
- `dmis-lab/biobert-v1.1`
- `dmis-lab/biobert-large-cased-v1.1`
- `microsoft/BiomedNLP-PubMedBERT-base-uncased-abstract-fulltext`

## Data Format

### Input Data
- **Abstracts**: Plain text files (`.txt`) containing PubMed abstracts
- **Annotations**: Corresponding annotation files (`.ann`) with entity labels

### Output Format
- **NER**: BIO/BIOES tagged sequences
- **RE**: Classified entity relationships
- **Dataset extraction**: Enhanced abstracts with identified dataset mentions

## Performance

The models achieve competitive performance on biomedical NER and RE tasks:
- **NER F1 Score**: >85% on biomedical datasets
- **RE Accuracy**: >80% on relation classification
- **Dataset Detection**: High precision in identifying relevant datasets

## License

This project is for research purposes. Please cite appropriately if used in academic work.

## Contributing

1. Fork the repository
2. Create a feature branch
3. Make your changes
4. Submit a pull request

## Support

For issues or questions, please create an issue in the GitHub repository.