import random
import os

random.seed(42)


def sample(name, number):
    with open(f"{folder_path}/{name}.txt", "r") as file:
        data = file.readlines()
    sampled_id_list = random.sample(data, number)

    for i in sampled_id_list:
        with open(f"{target_path}/{name}.txt", "a") as file:
            file.write(f"{i}")

    with open(f"{target_path}/{name}.txt", "r") as file:
        data_ = file.readlines()
    print(f"{name}: {len(data)}, {len(data_)}")


folder_path = (
    "/home/gy237/project/Biomedical_datasets/extraction_pipeline/id_list/new_id_list"
)
all_items = os.listdir(folder_path)
target_path = "/home/gy237/project/Biomedical_datasets/extraction_pipeline/sampled_id_list/new_sampled_id"
# for file in all_items:
#     name = file.split('.')[0]

sample("biosamples", 100)
sample("clinical_trials", 100)
sample("diseases", 100)
sample("genotypes_phenotypes", 100)
sample("microscopy_images", 100)
sample("pathways", 100)
