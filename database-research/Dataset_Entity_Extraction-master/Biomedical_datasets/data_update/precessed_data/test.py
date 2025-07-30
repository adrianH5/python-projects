import json

_type_ = ["train", "test", "devel"]

dataset = []
rep = []
for _type in _type_:
    # if True:
    #     _type = 'test'
    with open(
        f"/home/gy237/project/Biomedical_datasets/data_update/precessed_data/{_type}_data.json",
        "r",
        encoding="utf-8",
    ) as file:
        data = json.load(file)

    for sentence in data:
        sens = sentence["sen"]
        lebs = sentence["lab"]
        for i in range(len(sens)):
            if lebs[i] and lebs[i]["type"] == "Dataset":
                dataset.append(sens[i])
            if lebs[i] and lebs[i]["type"] == "Repository":
                rep.append(sens[i])

print(f"set(Dataset): {len(set(dataset))}")
# print(set(dataset))
print(f"set(Repository): {len(set(rep))}")
print(f"Dataset number: {len(dataset)}")
print(f"Repository number: {len(rep)}")
# print(set(dataset))
count = 0
for i in dataset:
    if "GISAID" in i:
        count += 1
print(f"Number of GISAID: {count}")
print(f"GISAID percent: {count/len(dataset)}")
# print(rep)
# print(dataset)
print(set(dataset))
print(set(rep))
