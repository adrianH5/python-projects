import os
from openai import OpenAI
from dotenv import load_dotenv


def find_dataset_mentions_with_gpt(abstracts_dir, output_dir, limit=300):
    """
    Uses GPT-4o to find mentions of dataset repositories in ALL downloaded PubMed abstracts,
    then saves the top 'limit' longest abstracts that contain datasets.

    Args:
        abstracts_dir (str): The directory containing the abstract files.
        output_dir (str): The directory where processed files will be saved.
        limit (int): Maximum number of abstracts with datasets to save (default: 300)
    """
    load_dotenv()
    api_key = os.getenv("OPENAI_API_KEY")
    if not api_key or api_key == "YOUR_API_KEY":
        print("Error: The OPENAI_API_KEY is not set in the .env file.")
        return

    client = OpenAI(api_key=api_key)

    # Create output directory if it doesn't exist
    os.makedirs(output_dir, exist_ok=True)

    # Get all txt files with their sizes
    all_files = []
    for filename in os.listdir(abstracts_dir):
        if filename.endswith(".txt"):
            file_path = os.path.join(abstracts_dir, filename)
            try:
                with open(file_path, "r") as f:
                    content = f.read()
                    all_files.append((filename, len(content), file_path))
            except Exception as e:
                print(f"Error reading {filename}: {e}")

    print(f"Processing ALL {len(all_files)} abstracts to find dataset mentions...")
    print(f"Will save top {limit} longest abstracts that contain datasets")
    print(f"Output directory: {output_dir}")
    print()

    processed_count = 0
    abstracts_with_datasets = []  # Store abstracts that contain datasets

    for filename, size, file_path in all_files:
        output_path = os.path.join(output_dir, filename)

        # Check if already processed
        if os.path.exists(output_path):
            print(f"Skipping {filename} - already processed")
            # Still need to add to our dataset list for final selection
            with open(output_path, "r") as f:
                content = f.read()
                abstracts_with_datasets.append((filename, size, file_path, content))
            continue

        with open(file_path, "r") as f:
            content = f.read()

        prompt = f"Please identify any dataset mentions in the following text. If a dataset is found, please list it. If no dataset is found, please write 'No dataset found'.\n\n{content}"

        try:
            response = client.chat.completions.create(
                model="gpt-4o",
                messages=[
                    {
                        "role": "system",
                        "content": "You are a helpful assistant that identifies dataset mentions in text.",
                    },
                    {"role": "user", "content": prompt},
                ],
            )

            dataset_mentions = response.choices[0].message.content.strip()

            # If datasets were found, add to our list
            if dataset_mentions and "no dataset found" not in dataset_mentions.lower():
                enhanced_content = content + f"\nY: {dataset_mentions}"
                abstracts_with_datasets.append(
                    (filename, size, file_path, enhanced_content)
                )
                print(f"Found datasets in {filename} ({size} chars)")
            else:
                print(f"No dataset found in {filename}")

            processed_count += 1

        except Exception as e:
            print(f"An error occurred while processing {filename}: {e}")

    print(f"\nProcessed {processed_count} abstracts")
    print(f"Found datasets in {len(abstracts_with_datasets)} abstracts")

    # Sort abstracts with datasets by size (descending) and take top 'limit'
    abstracts_with_datasets.sort(key=lambda x: x[1], reverse=True)
    top_dataset_abstracts = abstracts_with_datasets[:limit]

    print(f"Selecting top {len(top_dataset_abstracts)} longest abstracts with datasets")
    if top_dataset_abstracts:
        print(
            f"Longest: {top_dataset_abstracts[0][0]} ({top_dataset_abstracts[0][1]} characters)"
        )
        print(
            f"Shortest: {top_dataset_abstracts[-1][0]} ({top_dataset_abstracts[-1][1]} characters)"
        )

    # Save the selected abstracts
    saved_count = 0
    for filename, size, file_path, enhanced_content in top_dataset_abstracts:
        output_path = os.path.join(output_dir, filename)
        if not os.path.exists(output_path):  # Only write if not already exists
            with open(output_path, "w") as f:
                f.write(enhanced_content)
            saved_count += 1

    print(f"\nSaved {saved_count} new abstracts with datasets")
    print(
        f"Total abstracts with datasets in output directory: {len(top_dataset_abstracts)}"
    )
    print(f"Results saved in: {output_dir}")


if __name__ == "__main__":
    abstracts_directory = (
        "../pubmed_abstracts"  # Adjusted path since script is in subdirectory
    )
    output_directory = "../abstracts_with_datasets_top300"  # Output directory for abstracts with datasets only
    find_dataset_mentions_with_gpt(abstracts_directory, output_directory, limit=300)
