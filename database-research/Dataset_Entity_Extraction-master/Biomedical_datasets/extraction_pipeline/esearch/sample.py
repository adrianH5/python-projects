import random
import os

random.seed(42)

# def sample(name, number):
#     with open(f'{folder_path}/{name}.txt', 'r') as file:
#         data = file.readlines()

#     sampled_id_list = random.sample(data, number)

#     with open(f'{p1}/{name}.txt', 'w') as file:
#         for i in sampled_id_list[:10]:
#             file.write(f'{i}')
#     with open(f'{p2}/{name}.txt', 'w') as file:
#         for i in sampled_id_list[10:]:
#             file.write(f'{i}')

#     with open(f'{p1}/{name}.txt', 'r') as file:
#         data_ = file.readlines()
#     with open(f'{p2}/{name}.txt', 'r') as file:
#         _data_ = file.readlines()
#     print(f'{name}: {len(data)}, {len(data_)}, {len(_data_)}')

# folder_path = '/home/gy237/project/Biomedical_datasets/extraction_pipeline/esearch/PMCID'
# all_items = os.listdir(folder_path)
# target_path = '/home/gy237/project/Biomedical_datasets/extraction_pipeline/esearch/pmcid_sample'
# p1 = '/home/gy237/project/Biomedical_datasets/extraction_pipeline/esearch/pmcid_sample_gui'
# p2 = '/home/gy237/project/Biomedical_datasets/extraction_pipeline/esearch/pmcid_sample_kalpana'

# for file in all_items:
#     name = file.split('.')[0]
#     sample(name, 20)

# # print(all_items)
# print(len(all_items))


def sample(name, number):
    with open(f"{f1}/{name}.txt", "r") as file:
        data = file.readlines()
    with open(f"{f2}/{name}.txt", "r") as file:
        data += file.readlines()

    sampled_id_list = []
    for i in ["PMC11231869", "PMC2519326", "PMC8683552", "PMC4244250", "PMC4047826"]:
        if i in data:
            number -= 1
            sampled_id_list += [i]

    sampled_id_list += random.sample(data, number)

    return sampled_id_list


f1 = "/home/gy237/project/Biomedical_datasets/extraction_pipeline/esearch/pmcid_sample_gui"
all_items = os.listdir(f1)
all_items = [i.split(".")[0] for i in all_items]
f2 = "/home/gy237/project/Biomedical_datasets/extraction_pipeline/esearch/pmcid_sample_gui"
print(len(all_items))


_list = []
for name in [
    "genbank_pmcid",
    "gene_expression_omnibus_pmcid",
    "pubchem_pmcid",
    "protein_data_bank_pmcid",
    "uniprot_pmcid",
]:
    _list += sample(name, 5)
print(len(_list))

for name in ["clinical_trials_pmcid"]:
    _list += sample(name, 6)
print(len(_list))

for name in all_items:
    if name not in [
        "clinical_trials_pmcid",
        "genbank_pmcid",
        "gene_expression_omnibus_pmcid",
        "pubchem_pmcid",
        "protein_data_bank_pmcid",
        "uniprot_pmcid",
    ]:
        _list += sample(name, 3)

# print(_list)
print(len(_list))
_list = [i.strip() for i in _list]

import csv

with open(
    "/home/gy237/project/Biomedical_datasets/extraction_pipeline/esearch/gui_50.csv",
    mode="w",
    newline="",
    encoding="utf-8",
) as file:
    writer = csv.writer(file)
    for item in _list[:50]:
        writer.writerow([item])  # 每个元素作为一行写入
with open(
    "/home/gy237/project/Biomedical_datasets/extraction_pipeline/esearch/kalpana_50.csv",
    mode="w",
    newline="",
    encoding="utf-8",
) as file:
    writer = csv.writer(file)
    for item in _list[50:]:
        writer.writerow([item])  # 每个元素作为一行写入
