import os
import random

random.seed(42)

folder_path = "/home/gy237/project/Biomedical_datasets/data_update/row_data_updated"


id_list = []
# 获取文件夹下的所有文件和子文件夹
all_files = os.listdir(folder_path)
print(len(all_files))
for i in all_files:
    if i.endswith(".ann") or i.endswith(".txt"):
        _id = i.split(".")[0]
        if _id not in id_list:
            id_list += [_id]
print(f"Total PubMed id: {len(id_list)}")

train_id = random.sample(id_list, int(len(id_list) * 0.8))
print(f"Train id: {len(train_id)}")

# _test_id = []
# for i in id_list:
#     if i not in train_id:
#         _test_id += [i]
# print(len(_test_id))

# test_id = random.sample(_test_id, int(len(_test_id) * 0.5))
# print(f'Test id: {len(test_id)}')

# devel_id = []
# for i in _test_id:
#     if i not in test_id:
#         devel_id += [i]
# print(f'devel id: {len(devel_id)}')

# train_folder = '/home/gy237/project/Biomedical_datasets/data_update/train_data_updated'
# for i in train_id:
#     shutil.copy(f'{folder_path}/{i}.ann', train_folder)
#     shutil.copy(f'{folder_path}/{i}.txt', train_folder)

# test_folder = '/home/gy237/project/Biomedical_datasets/data_update/test_data_updated'
# for i in test_id:
#     shutil.copy(f'{folder_path}/{i}.ann', test_folder)
#     shutil.copy(f'{folder_path}/{i}.txt', test_folder)

# devel_folder = '/home/gy237/project/Biomedical_datasets/data_update/devel_data_updated'
# for i in devel_id:
#     shutil.copy(f'{folder_path}/{i}.ann', devel_folder)
#     shutil.copy(f'{folder_path}/{i}.txt', devel_folder)

# train_file = os.listdir(train_folder)
# test_file = os.listdir(test_folder)
# devel_file = os.listdir(devel_folder)
# print(len(train_file))
# print(len(test_file))
# print(len(devel_file))

# for i in train_file + devel_file:
#     if i in test_file:
#         print(i)

# for i in train_file + test_file:
#     if i in devel_file:
#         print(i)

# print(sorted(train_file)[:5])
# print(sorted(test_file)[:5])
