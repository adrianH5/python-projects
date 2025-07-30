import os
import spacy
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


# load spacy model
nlp = spacy.load("en_core_web_sm")


def tokenize_sentence(sentence):
    # use spacy to token
    doc = nlp(sentence)
    return [token.text for token in doc]


word_list = []
label_list = []
for _id in data_id:
    # if True:
    #     _id = data_id[3]  #'PMC7228217'
    entities = parse_ann_file(f"{path}/{_id}.ann")

    with open(f"{path}/{_id}.txt", "r", encoding="utf-8") as f:
        text = f.read().replace("\n", " ")

    # check the index and the name
    for _ent in entities:
        if _ent["name"] != text[_ent["start"] : _ent["end"]]:
            print(_id)  # PMC7366180, PMC7441778

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

    # first tokenize
    for i in range(len(bool_list)):
        if bool_list[i] == False:
            _word_list = tokenize_sentence(text_list[i])
            label_list += [bool_list[i]] * len(_word_list)
            word_list += _word_list
        else:
            _word_list = text_list[i].split(" ")
            label_list += [bool_list[i]] * (len(_word_list))
            # if len(_word_list) == 1:
            #     label_list += [f'S-{bool_list[i]}']
            # else:
            #     label_list = label_list + [f'B-{bool_list[i]}'] + [f'I-{bool_list[i]}']*(len(_word_list) - 2) + [f'E-{bool_list[i]}']

            word_list += _word_list

if len(word_list) != len(label_list):
    print("Error")


def vet_frases(word, label):
    sentences = []
    sentences_aux = []
    labels = []
    labels_aux = []
    for word, label in zip(word, label):
        sentences_aux.append(word)
        labels_aux.append(label)
        if word == ".":
            sentences.append(sentences_aux)
            labels.append(labels_aux)

            sentences_aux = []
            labels_aux = []
    return sentences, labels


sentences, labels = vet_frases(word_list, label_list)

# with open(f'/home/gy237/project/Biomedical_datasets/NER/data/{_type}_data.csv', 'w', newline='', encoding='utf-8') as file:
#     writer = csv.writer(file)
#     for item1, item2 in zip(word_list, label_list):
#         writer.writerow([item1, item2])
# print('over')

data_list = []
for i in range(len(sentences)):
    dct = {"sen": sentences[i], "lab": labels[i]}
    data_list.append(dct)

with open(
    f"/home/gy237/project/Biomedical_datasets/NER/data/{_type}_data.json",
    "w",
    encoding="utf-8",
) as file:
    json.dump(data_list, file, ensure_ascii=False, indent=4)
