import re


def clean(name):

    with open(f"{folder_path}/{name}.txt", "r") as file:
        data = file.readlines()

    for i in data:
        _id = ""
        _id_ = ""
        id_ = i.strip()

        id_list_ = id_.split(":")
        for j in id_list_:
            id_list = j.split(",")
            for k in id_list:
                if k.startswith("PMC"):
                    _id = k

        pattern = r"PMC\d+"
        match = re.search(pattern, id_)
        if match:
            _id_ = match.group()

        assert _id == _id_
        if _id != "":
            with open(
                f"/home/gy237/project/Biomedical_datasets/extraction_pipeline/id_list/new_id_list/{name}.txt",
                "a",
            ) as file:
                file.write(f"{_id}\n")


import os

folder_path = "/home/gy237/project/Biomedical_datasets/extraction_pipeline/id_list/new_raw_id_list"
all_items = os.listdir(folder_path)

for file in all_items:
    name = file.split(".")[0]
    clean(name)

# clean('biosample')
