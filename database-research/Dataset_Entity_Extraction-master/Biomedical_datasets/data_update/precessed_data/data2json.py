import os
import json

_type = "train"
path = f"/home/gy237/project/Biomedical_datasets/data_update/{_type}_data_updated"
files = os.listdir(path)
print(len(files))


# get the unique id
data_id = []
for i in files:
    _id = i.split(".")[0]
    if _id not in data_id:
        data_id += [_id]
print(len(data_id))


# get entities from annoation
def parse_ann_file(ann_file_path):
    entities = []
    relations = []
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

            if line.startswith("R"):
                parts = line.split("\t")
                relation = {
                    "id": parts[0],
                    "bool": parts[1] == "hasAttr",
                    "head": parts[2].split(":")[1],
                    "end": parts[3].split(":")[1],
                }
                relations.append(relation)

    return entities, relations


def find_sent_relation(sent, sent_label_list, relations):
    rela_list = []
    for i in range(len(sent_label_list)):
        if sent_label_list[i]:
            for rela in relations:
                if rela["head"] == sent_label_list[i]["id"]:
                    rela_list.append(rela)
    if len(rela_list) > 0:
        return rela_list
    else:
        return ["No Relation"]


data_list = []
for _id in data_id:
    # if True:
    #     _id = 'PMC7094943'  #'PMC7228217'
    entities, relations = parse_ann_file(f"{path}/{_id}.ann")

    with open(f"{path}/{_id}.txt", "r", encoding="utf-8") as f:
        text = f.read()

    # check the index and the name
    for _ent in entities:
        if _ent["name"] != text[_ent["start"] : _ent["end"]]:
            print(_ent["name"])
            print(
                text[_ent["start"] : _ent["end"]]
            )  # PMC7471802, PMC7366180, PMC7441778, PMC7252096, PMC7354438
            print(f"{_id}_entity_name_error")
    for i in relations:
        if i["bool"] == False or i["head"][0] != "T" or i["end"][0] != "T":
            print("error")

    # get the label bool list
    text_list = []
    bool_list = []
    if len(entities) != 0:
        for i in range(len(entities)):
            if i == 0:
                text_list += [text[: entities[i]["start"]]]
            else:
                text_list += [text[entities[i - 1]["end"] : entities[i]["start"]]]
            bool_list += [False]

            text_list += [text[entities[i]["start"] : entities[i]["end"]]]
            bool_list += [entities[i]]

            if i == len(entities) - 1:
                text_list += [text[entities[i]["end"] :]]
                bool_list += [False]
    else:
        text_list += [text]
        bool_list += [False]

    if len(text_list) != 2 * len(entities) + 1 or len(bool_list) != len(
        text_list
    ):  # check the number
        print(_id)

    sentences = []
    sen = []
    label_list = []
    _label = []
    for i in range(len(bool_list)):
        if "\n" not in text_list[i]:
            sen += [text_list[i]]
            _label += [bool_list[i]]
        else:
            tests = text_list[i].split("\n")
            for j in range(len(tests)):
                if j != len(tests) - 1:
                    sen += [tests[j]]
                    sentences += [sen]
                    sen = []

                    _label += [bool_list[i]]
                    label_list += [_label]
                    _label = []
                else:
                    sen += [tests[j]]
                    _label += [bool_list[i]]

    sentences += [sen]
    label_list += [_label]

    if len(sentences) == 0:
        print("sentences == 0")

    for i in range(len(label_list)):
        for j in range(len(label_list[i])):
            if label_list[i][j]:
                if sentences[i][j] != label_list[i][j]["name"]:
                    print("Error")

    _sentences = []
    _label_list = []
    cha = 0
    for i in range(len(sentences)):
        if sentences[i][-1].endswith("."):
            _sentences.append(sentences[i])
            _label_list.append(label_list[i])
        else:
            if len(sentences) == 1:
                _sentences.append(sentences[i])
                _label_list.append(label_list[i])
            elif i == 0:
                sentences[i + 1] = sentences[i] + sentences[i + 1]
                label_list[i + 1] = label_list[i] + label_list[i + 1]
                cha += 1
            elif i == len(sentences) - 1:
                _sentences[-1] = _sentences[-1] + sentences[i]
                _label_list[-1] = _label_list[-1] + label_list[i]
                cha += 1
            elif len(_sentences) == 0:
                sentences[i + 1] = sentences[i] + sentences[i + 1]
                label_list[i + 1] = label_list[i] + label_list[i + 1]
                cha += 1
            elif _sentences[-1][-1].endswith("."):
                sentences[i + 1] = sentences[i] + sentences[i + 1]
                label_list[i + 1] = label_list[i] + label_list[i + 1]
                cha += 1
            else:
                _sentences[-1] = _sentences[-1] + sentences[i]
                _label_list[-1] = _label_list[-1] + label_list[i]
                cha += 1

    if len(_sentences) + cha != len(sentences) or len(_sentences) != len(_label_list):
        print("len error")

    total_rel = 0
    for i in range(len(_sentences)):
        relation_list = find_sent_relation(_sentences[i], _label_list[i], relations)
        dic = {"sen": _sentences[i], "lab": _label_list[i], "rel": relation_list}
        data_list += [dic]

        total_rel += len([i for i in relation_list if i != "No Relation"])

    if total_rel != len(relations):
        print(total_rel)
        print(relations)

with open(
    f"/home/gy237/project/Biomedical_datasets/data_update/precessed_data/{_type}_data.json",
    "w",
    encoding="utf-8",
) as file:
    json.dump(data_list, file, ensure_ascii=False, indent=4)

    # with open(f'/home/gy237/project/Biomedical_datasets/RE/nospacy_data/{_type}_data.csv', 'a', newline='', encoding='utf-8') as file:
    #     writer = csv.writer(file)
    #     writer.writerow([_sentences[i], _label_list[i], relation_list])

# print(sentences)
# print(label_list)


# print(text_list)
# print(bool_list)
# print(sentences)
