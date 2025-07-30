import requests
import nltk
import os
import xml.etree.ElementTree as ET

# Download the sentence tokenizer model (only needs to be done once)
try:
    nltk.data.find("tokenizers/punkt")
except nltk.downloader.DownloadError:
    nltk.download("punkt")


def get_pubmed_abstracts(search_term, sample_size=500):
    """
    Searches PubMed for a given term, fetches the abstracts, and returns a list of dictionaries.

    Args:
        search_term (str): The term to search for on PubMed.
        sample_size (int): The number of articles to fetch.

    Returns:
        list: A list of dictionaries, where each dictionary contains the 'pmid' and 'abstract'.
    """
    base_url = "https://eutils.ncbi.nlm.nih.gov/entrez/eutils/"
    search_url = f"{base_url}esearch.fcgi"
    fetch_url = f"{base_url}efetch.fcgi"

    # Get the total number of articles
    search_params = {
        "db": "pubmed",
        "term": search_term,
        "retmax": 0,
        "usehistory": "y",
    }
    search_response = requests.get(search_url, params=search_params)
    search_root = ET.fromstring(search_response.content)
    total_articles = int(search_root.find("Count").text)
    webenv = search_root.find("WebEnv").text
    query_key = search_root.find("QueryKey").text

    print(f"Found {total_articles} articles for the search term '{search_term}'.")

    # Fetch all article IDs
    articles_to_fetch = min(total_articles, sample_size)
    batch_size = 500
    all_pmids = []

    for i in range(0, articles_to_fetch, batch_size):
        search_params = {
            "db": "pubmed",
            "term": search_term,
            "retstart": i,
            "retmax": batch_size,
            "usehistory": "y",
            "WebEnv": webenv,
            "query_key": query_key,
        }
        search_response = requests.get(search_url, params=search_params)
        search_root = ET.fromstring(search_response.content)
        pmids = [p.text for p in search_root.findall(".//Id")]
        all_pmids.extend(pmids)

    # Fetch the abstracts in batches
    articles = []
    for i in range(0, len(all_pmids), batch_size):
        pmid_batch = all_pmids[i : i + batch_size]
        fetch_params = {
            "db": "pubmed",
            "id": ",".join(pmid_batch),
            "rettype": "abstract",
            "retmode": "xml",
        }
        fetch_response = requests.get(fetch_url, params=fetch_params)
        fetch_root = ET.fromstring(fetch_response.content)

        for article in fetch_root.findall(".//PubmedArticle"):
            pmid = article.find(".//PMID").text
            abstract_element = article.find(".//Abstract/AbstractText")
            if abstract_element is not None:
                abstract = abstract_element.text
                articles.append({"pmid": pmid, "abstract": abstract})

    return articles


def process_pubmed_abstracts(articles, output_dir):
    """
    Processes PubMed abstracts, and saves each abstract's sentences to a separate file.

    Args:
        articles (list): A list of dictionaries, where each dictionary contains the 'pmid' and 'abstract'.
        output_dir (str): The directory where the output files will be saved.
    """
    # Create the output directory if it doesn't exist
    if not os.path.exists(output_dir):
        os.makedirs(output_dir)

    # Process each article
    for article in articles:
        pmid = article.get("pmid")
        abstract = article.get("abstract")

        if pmid and abstract:
            # Create a file for the abstract
            output_filename = os.path.join(output_dir, f"{pmid}.txt")

            # Split the abstract into sentences
            sentences = nltk.sent_tokenize(abstract)

            # Write each sentence to a new line in the file
            with open(output_filename, "w") as f:
                for sentence in sentences:
                    f.write(sentence + "\n")

    print(
        f"Successfully processed {len(articles)} articles. Files are saved in {output_dir}"
    )


if __name__ == "__main__":
    search_term = "cancer"  # You can change this to any search term
    output_directory = "pubmed_abstracts"

    articles = get_pubmed_abstracts(search_term)
    process_pubmed_abstracts(articles, output_directory)
