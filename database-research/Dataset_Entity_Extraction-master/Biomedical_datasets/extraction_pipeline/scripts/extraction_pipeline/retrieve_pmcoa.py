import requests
import os
import time
import pandas as pd

# Replace 'YOUR_EMAIL' with your email address
email = "YOUR_EMAIL"


# Define a function to download the full-text articles with rate limiting
def download_pmc_article(pmc_id):
    base_url = "https://eutils.ncbi.nlm.nih.gov/entrez/eutils/efetch.fcgi"

    # Parameters for the request
    params = {"db": "pmc", "id": pmc_id, "retmode": "xml"}

    # Check if the XML file already exists
    file_name = f"PMC_articles/{pmc_id}.xml"
    if os.path.exists(file_name):
        print(f"{pmc_id} already exists, skipping download.")
        return

    # Make the request
    response = requests.get(base_url, params=params)

    if response.status_code == 200:
        # Create a directory to store the articles
        if not os.path.exists("PMC_articles"):
            os.mkdir("PMC_articles")

        # Save the article as XML
        with open(file_name, "wb") as file:
            file.write(response.content)
        print(f"{pmc_id} downloaded successfully.")
    else:
        print(f"Error downloading {pmc_id}. Status code: {response.status_code}")

    # Rate limiting: Sleep for a few seconds before making the next request
    time.sleep(1)


# Read PMCID values from the Excel file
file_path = "csv-genomicsOR-set.xlsx"  # Replace with the path to your Excel file
df = pd.read_excel(file_path)

# Extract PMCID values from the "PMCID" column
pmc_ids = df["PMCID"].tolist()

# Loop through the list of PMCIDs and download the articles
for pmc_id in pmc_ids:
    download_pmc_article(pmc_id)
