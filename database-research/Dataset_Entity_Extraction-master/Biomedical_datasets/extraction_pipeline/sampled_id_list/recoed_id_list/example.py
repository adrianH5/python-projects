import random
import os

random.seed(42)

# def sample(name, number):
#     with open(f'{folder_path}/{name}.txt', 'r') as file:
#         data = file.readlines()
#     sampled_id_list = random.sample(data, number)

#     for i in sampled_id_list[:5]:
#         with open(f'{target_path_k}/{name}.txt', 'a') as file:
#             file.write(f'{i}')
#     for i in sampled_id_list[5:]:
#         with open(f'{target_path_g}/{name}.txt', 'a') as file:
#             file.write(f'{i}')

#     with open(f'{target_path_k}/{name}.txt', 'r') as file:
#         data_ = file.readlines()
#     print(f'{name}: {len(data)}, {len(data_)}')

# folder_path = '/home/gy237/project/Biomedical_datasets/extraction_pipeline/sampled_id_list/new_sampled_id'
# all_items = os.listdir(folder_path)
# target_path_k = '/home/gy237/project/Biomedical_datasets/extraction_pipeline/sampled_id_list/recoed_id_list/Kalpana'
# target_path_g = '/home/gy237/project/Biomedical_datasets/extraction_pipeline/sampled_id_list/recoed_id_list/gui'
# # for file in all_items:
# #     name = file.split('.')[0]

# sample('biosamples', 10)
# sample('clinical_trials', 10)
# sample('diseases', 10)
# sample('genotypes_phenotypes', 10)
# sample('microscopy_images', 10)
# sample('pathways', 10)


def chong(path):
    folder_path = path
    file_names = os.listdir(folder_path)
    input_names = [i.split(".")[0] for i in file_names if i.endswith("txt")]
    print(len(input_names))
    data = []
    for i in input_names:
        with open(f"{path}/{i}.txt") as f:
            data.extend(f.readlines())
    return data


data = chong(
    "/home/gy237/project/Biomedical_datasets/extraction_pipeline/sampled_id_list/new_sampled_id"
)
# data2 = chong('/home/gy237/project/Biomedical_datasets/extraction_pipeline/sampled_id_list/recoed_id_list/gui')
# data = data1 + data2
print(len(data))
print(len(set(data)))
