import os

_type = "row"
path = f"/home/gy237/project/Biomedical_datasets/data_update/{_type}_data_updated"
files = os.listdir(path)
print(len(files))


# get the unique id
ann_id = []
txt_id = []
for i in files:
    if i.endswith(".ann"):
        _id = i.split(".")[0]
        if _id not in ann_id:
            ann_id += [_id]
    if i.endswith(".txt"):
        _id = i.split(".")[0]
        if _id not in txt_id:
            txt_id += [_id]
print(len(ann_id))
print(len(txt_id))


# get entities from annoation
def parse_ann_file(ann_file_path):
    entities = []
    with open(ann_file_path, "r", encoding="utf-8") as file:
        for line in file:
            line = line.strip()
            if line.startswith("T"):
                # Entity line: T1\tEntityType start end\tName
                parts = line.split("\t")
                entity_id = parts[0]
                entity_info = parts[1]
                entity_name = parts[2]

                entity_type, start, end = entity_info.split(" ")
                entity = {
                    "id": entity_id,
                    "type": entity_type,
                    "start": int(start),
                    "end": int(end),
                    "name": entity_name,
                }

                entities.append(entity)

    return entities


entity_dic = {}
for _id in ann_id:
    # if True:
    #     _id = data_id[3]  #'PMC7228217'
    entities = parse_ann_file(f"{path}/{_id}.ann")
    # with open(f'{path}/{_id}.ann', 'r') as f:
    #     text = f.read()
    #     pattern = re.compile(r'\bdoi\b', re.IGNORECASE)
    #     matches = pattern.findall(text)
    # if matches:
    #     print(matches)
    #     print(_id)

    for i in entities:
        en_type = i["type"]
        if en_type not in entity_dic.keys():
            entity_dic[en_type] = 0
        else:
            entity_dic[en_type] += 1
print(entity_dic)
