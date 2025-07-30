import numpy as np
import torch
from torch.utils.data import TensorDataset, DataLoader, RandomSampler
from transformers import BertTokenizerFast
from tensorflow.keras.preprocessing.sequence import pad_sequences
from transformers import BertForSequenceClassification
from seqeval.metrics import f1_score, accuracy_score
from seqeval.metrics import classification_report
import os
import json
import random

torch.cuda.init()
ner_imfile = "/home/gy237/project/Biomedical_datasets/NER/nerbert/biobert-large-cased-v1.1_output/time_8"
re_imfile = "/home/gy237/project/Biomedical_datasets/RE/biobert-v1.1_output/time_14"

# NER
with open(f"{ner_imfile}/hyperparameter.json", "r", encoding="utf-8") as file:
    hp = json.load(file)

MAX_LEN = hp["MAX_LEN"]
if "SEED" in hp.keys():
    SEED = hp["SEED"]
do_lower_case = hp["do_lower_case"]
add_token = hp["add_token"]
model_name = hp["model_name"]


_name = model_name.split("/")[-1]
outfile = f"/home/gy237/project/Biomedical_datasets/combined/{_name}"
if not os.path.exists(outfile):
    os.makedirs(outfile)
all_files = os.listdir(outfile)
time = len(all_files)
outfile = outfile + f"/time_{time}"
os.makedirs(outfile, exist_ok=True)

# copy sth to outfile
hp["ner_import_model_file"] = ner_imfile
with open(f"{outfile}/ner_hyperparameter.json", "w", encoding="utf-8") as json_file:
    json.dump(hp, json_file, indent=4, ensure_ascii=False)

if add_token:
    tokenizer = BertTokenizerFast.from_pretrained(
        f"{ner_imfile}/tokenizer_file", do_lower_case=do_lower_case
    )
    print("Finish loading NER_tokenizer")
else:
    tokenizer = BertTokenizerFast.from_pretrained(
        model_name, do_lower_case=do_lower_case, local_files_only=True
    )


# RE
with open(f"{re_imfile}/hyperparameter.json", "r", encoding="utf-8") as file:
    re_hp = json.load(file)

re_MAX_LEN = re_hp["MAX_LEN"]
re_do_lower_case = re_hp["do_lower_case"]
SEED = re_hp["Seed"]
re_add_token = re_hp["add_token"]
re_model_name = re_hp["model_name"]

# copy sth to outfile
re_hp["re_import_model_file"] = re_imfile
with open(f"{outfile}/re_hyperparameter.json", "w", encoding="utf-8") as json_file:
    json.dump(re_hp, json_file, indent=4, ensure_ascii=False)

if re_add_token:
    re_tokenizer = BertTokenizerFast.from_pretrained(
        f"{re_imfile}/tokenizer_file", do_lower_case=re_do_lower_case
    )
    print("Finish loading RE_tokenizer")
else:
    re_tokenizer = BertTokenizerFast.from_pretrained(
        re_model_name, do_lower_case=re_do_lower_case, local_files_only=True
    )


random.seed(SEED)
np.random.seed(SEED)
torch.manual_seed(SEED)
if torch.cuda.is_available():
    torch.cuda.manual_seed_all(SEED)


with open(
    "/home/gy237/project/Biomedical_datasets/data_update/precessed_data/test_data.json",
    "r",
    encoding="utf-8",
) as file:
    devel_data = json.load(file)
    # train_data = [ json.load(line) for line in data_list ]
    devel_sen = [i["sen"] for i in devel_data]
    devel_lab = [i["lab"] for i in devel_data]
    devel_rel = [i["rel"] for i in devel_data]

if "focus_on_dataset" in hp.keys() and hp["focus_on_dataset"]:
    for i in range(len(devel_lab)):
        for j in range(len(devel_lab[i])):
            if devel_lab[i][j]:
                if devel_lab[i][j]["type"] != "Dataset":
                    devel_lab[i][j] = False

label = {}
for i in devel_lab:
    for j in i:
        if j:
            if j["type"] in label:
                label[j["type"]] += 1
            else:
                label[j["type"]] = 1
print(label)

# tag2idx
with open(f"{ner_imfile}/tag2idx.json", "r", encoding="utf-8") as file:
    tag2idx = json.load(file)

idx2tag = {i: t for t, i in tag2idx.items()}
print(idx2tag)
print("--------------------------------------------")


# to cuda
device = torch.device("cuda" if torch.cuda.is_available() else "cpu")
torch.manual_seed(SEED)
torch.backends.cudnn.deterministic = True

# NER model
model_files = os.listdir(f"{ner_imfile}/saved_model")
best_f1 = 0
index = 0
for i in range(len(model_files)):
    if best_f1 < float(model_files[i].split("_")[-1].split(".pth")[0]):
        best_f1 = float(model_files[i].split("_")[-1].split(".pth")[0])
        index = i


model = torch.load(f"{ner_imfile}/saved_model/{model_files[index]}")
print(model_files[index])
model.cuda()


# re model
model_files = os.listdir(f"{re_imfile}/saved_model")
best_f1 = 0
index = 0
for i in range(len(model_files)):
    if best_f1 < float(model_files[i].split("_")[-1]):
        best_f1 = float(model_files[i].split("_")[-1])
        index = i

re_model = BertForSequenceClassification.from_pretrained(
    f"{re_imfile}/saved_model/{model_files[index]}",
    num_labels=2,
    output_attentions=False,
    output_hidden_states=False,
)


re_model.cuda()


def process_data(sentence, text_labels):
    tokenized_sentence = []
    labels = []
    tokenized_sentence.append("[CLS]")
    labels.append("O")

    for i in range(len(sentence)):
        tokenized_sen = tokenizer.tokenize(sentence[i])
        tokenized_sentence.extend(tokenized_sen)
        n_subwords = len(tokenized_sen)
        _labels = []
        if text_labels[i] == False:
            _labels = ["O"] * n_subwords
        else:
            label = text_labels[i]["type"]
            _labels = [f"B-{label}"] + [f"I-{label}"] * (n_subwords - 1)
            # if n_subwords == 1:
            #     _labels = [f'S-{label}']
            # else:
            #     _labels = [f'B-{label}'] + [f'I-{label}']*(n_subwords - 2) + [f'E-{label}']

        labels.extend(_labels)

    tokenized_sentence.append("[SEP]")
    labels.append("O")

    if len(tokenized_sentence) != len(labels):
        print(n_subwords)
        print(len(_labels))
        print(tokenized_sentence)
        print(labels)
        print("Error")

    # print(tokenized_sentence)
    # print(labels)
    # return tokenized_sentence, labels, relation

    sen_input_ids = pad_sequences(
        [tokenizer.convert_tokens_to_ids(tokenized_sentence)],
        maxlen=MAX_LEN,
        dtype="long",
        value=0.0,
        truncating="post",
        padding="post",
    )

    sen_tags = pad_sequences(
        [[tag2idx.get(l) for l in labels]],
        maxlen=MAX_LEN,
        value=tag2idx["PAD"],
        padding="post",
        dtype="long",
        truncating="post",
    )

    sen_attention_masks = [[float(i != 0.0) for i in ii] for ii in sen_input_ids]

    tr_inputs = torch.tensor(sen_input_ids)
    tr_tags = torch.tensor(sen_tags)
    tr_masks = torch.tensor(sen_attention_masks)

    devel_data = TensorDataset(tr_inputs, tr_masks, tr_tags)
    devel_sampler = RandomSampler(devel_data)
    devel_dataloader = DataLoader(devel_data, sampler=devel_sampler, batch_size=1)

    return devel_dataloader


with open(
    "/home/gy237/project/Biomedical_datasets/combined/special_characters.json",
    "r",
    encoding="utf-8",
) as file:
    special_characters = json.load(file)


def model_process(sen_dataloader):
    for batch in sen_dataloader:
        batch = tuple(t.to(device) for t in batch)
        b_input_ids, b_input_mask, b_labels = batch
        with torch.no_grad():
            outputs = model(
                b_input_ids,
                token_type_ids=None,
                attention_mask=b_input_mask,
                labels=b_labels,
            )

        logits = outputs[1].detach().cpu().numpy()
        label_ids = b_labels.to("cpu").numpy()
        input_ids = b_input_ids.to("cpu").numpy()

        _text = []
        text = []
        for i in input_ids:
            _text += tokenizer.convert_ids_to_tokens(i)
        for i in _text:
            if i != "[PAD]":
                text.append(i)

        preds_ids = [list(p) for p in np.argmax(logits, axis=2)]
        pred_tags = [
            idx2tag[p_i]
            for p, l in zip(preds_ids, label_ids)
            for p_i, l_i in zip(p, l)
            if idx2tag[l_i] != "PAD"
        ]
        valid_tags = [
            idx2tag[l_i] for l in label_ids for l_i in l if idx2tag[l_i] != "PAD"
        ]

        for i in range(len(pred_tags)):
            valid_tags[i] = valid_tags[i].split("-")[-1]
            pred_tags[i] = pred_tags[i].split("-")[-1]

        assert len(text) == len(pred_tags) == len(valid_tags), "254, Error"

    return text, pred_tags, valid_tags


devel_result = {}
predictions, true_labels, texts = [], [], []
eachWordPred, eachWordLab = [], []
raw_label = []
number_count = 0
label_count = 0
tokenized_sen = []
model.eval()
re_model.eval()
for idx in range(len(devel_sen)):
    sen_texts = devel_sen[idx]
    sen_labs = devel_lab[idx]
    sen_rels = devel_rel[idx]

    text = []
    pred_tags = []
    valid_tags = []

    # for i in range(len(sen_texts)):
    #     if len(token_list.extend(tokenizer.tokenize(sen_texts[i]))) > 120:

    token_list = []
    idx_list = []
    for i in range(len(sen_texts)):
        token_list.extend(tokenizer.tokenize(sen_texts[i]))
        if len(token_list) > 120:
            idx_list.append(i)
            token_list = []
            token_list.extend(tokenizer.tokenize(sen_texts[i]))

    if idx_list == []:
        sen_dataloader = process_data(sen_texts, sen_labs)
        text, pred_tags, valid_tags = model_process(sen_dataloader)
    else:
        if 0 not in idx_list:
            idx_list = [0] + idx_list

        for ix in range(len(idx_list) - 1):
            sen_dataloader = process_data(
                sen_texts[idx_list[ix] : idx_list[ix + 1]],
                sen_labs[idx_list[ix] : idx_list[ix + 1]],
            )
            _text, _pred_tags, _valid_tags = model_process(sen_dataloader)
            text.extend(_text)
            pred_tags.extend(_pred_tags)
            valid_tags.extend(_valid_tags)

            if ix == len(idx_list) - 2:
                sen_dataloader = process_data(
                    sen_texts[idx_list[ix + 1] :], sen_labs[idx_list[ix + 1] :]
                )
                _text, _pred_tags, _valid_tags = model_process(sen_dataloader)
                text.extend(_text)
                pred_tags.extend(_pred_tags)
                valid_tags.extend(_valid_tags)

    predictions.extend(pred_tags)
    true_labels.extend(valid_tags)
    tokenized_sen.extend(text)

    ## RE
    if True:
        # if len(sen_rels) > 1:
        raw_sen = "".join(sen_texts)
        texts.append(raw_sen)  #
        split_sen = []
        split_lab = []
        for i in range(len(sen_texts)):
            if " " in sen_texts[i]:
                _split_sen = [i for i in sen_texts[i].split(" ") if i]
                split_sen.extend(_split_sen)
                split_lab.extend([sen_labs[i]] * len(_split_sen))
            else:
                split_sen.append(sen_texts[i])
                split_lab.append(sen_labs[i])
        assert len(split_sen) == len(split_lab), "293 Error"

        model_lab = []
        model_pre = []
        x = 0
        for i in range(len(split_sen)):
            for k in special_characters:
                if k in split_sen[i]:
                    split_sen[i] = split_sen[i].replace(k, "")

            _lab = []
            _pre = []
            _sen = ""
            for j in range(x, len(text)):
                if text[j] == "[UNK]":
                    model_lab.append(valid_tags[j])
                    model_pre.append(pred_tags[j])
                    x = j + 1
                    break

                if text[j].startswith("##"):
                    _t = text[j][2:]
                else:
                    _t = text[j]

                if _t in split_sen[i]:
                    _sen += _t
                    # print(_sen)
                    # print(split_sen[i])
                if _sen in split_sen[i]:
                    _lab.append(valid_tags[j])
                    _pre.append(pred_tags[j])

                if _sen == split_sen[i]:
                    if _lab == []:
                        continue
                    else:
                        assert len(_lab) == len(_pre), "314 Error"
                        x = j + 1
                        if len(_pre) == 1:
                            model_lab.extend(_lab)
                            model_pre.extend(_pre)
                        else:
                            flag = True
                            for k in range(len(_pre)):
                                if _pre[k] != "O":
                                    flag = False
                                    gg = k
                            if flag:
                                model_pre.append("O")
                            else:
                                model_pre.append(_pre[gg])

                            flag = True
                            for k in range(len(_lab)):
                                if _lab[k] != "O":
                                    flag = False
                                    gg = k
                            if flag:
                                model_lab.append("O")
                            else:
                                model_lab.append(_lab[gg])
                    break

        if len(model_lab) != len(split_lab):
            # print(len(model_pre))
            # print(len(model_lab))
            # print(len(split_lab))

            model_lab.extend(["O"] * (len(split_lab) - len(model_lab)))
            model_pre.extend(["O"] * (len(split_lab) - len(model_pre)))
            number_count += 1
            # print(sen_texts)
            # print(sen_labs)
            # print(sen_rels)
            # print(text)
            # print(len(text))
            # print(valid_tags)
            # print(pred_tags)
            # print(split_sen)
            # print(split_lab)
            # print(model_pre)
            # print(model_lab)

            # exit()

        eachWordPred.extend(model_pre)
        eachWordLab.extend(model_lab)
        raw_label.extend(split_lab)

        for i in range(len(model_lab)):
            if split_lab[i]:
                if model_lab[i] != split_lab[i]["type"]:
                    label_count += 1

        # print(sen_texts)
        # print(sen_labs)
        # print(sen_rels)
        # print(text)
        # print(valid_tags)
        # print(pred_tags)
        # print(split_sen)
        # print(split_lab)
        # print(model_pre)
        # print(model_lab)
        # print(len(model_pre))
        # print(len(model_lab))
        # print(len(split_lab))
        # exit()

# ##拼在一起，如果完全相同就结束加入_pre了，标点符号可加进去，字母不加进去
# import re
# special_characters = []
# for item in texts:
#     # 查找所有非ASCII字符
#     matches = re.findall(r'[^\x00-\x7F]', item)
#     if matches:
#         special_characters.extend(matches)

# special_characters2 = []
# for item in tokenized_sen:
#     # 查找所有非ASCII字符
#     matches = re.findall(r'[^\x00-\x7F]', item)
#     if matches:
#         special_characters2.extend(matches)
# cha = []
# for i in special_characters:
#     if i not in special_characters2:
#         cha.append(i)
# print(cha)
# print(set(cha))
# print(len(cha))
# print(len(special_characters))
# print(len(special_characters2))
# exit()

print(number_count)
print(label_count)
report = classification_report(true_labels, predictions, digits=len(idx2tag.keys()))
print(report)
print("----------------------------------------------------------")
print(len(true_labels))
print(len(predictions))
_raw_label = []
for i in raw_label:
    if i:
        _raw_label.append(i["type"])
    else:
        _raw_label.append("O")

report2 = classification_report(_raw_label, eachWordPred, digits=len(idx2tag.keys()))
print(report2)

accuracy = accuracy_score(true_labels, predictions)
f1 = f1_score(true_labels, predictions, average="weighted")  # macro, weighted
f2 = f1_score(true_labels, predictions, average="macro")
print("Accuracy: {}".format(accuracy))
print("F1-Score-weighted: {}".format(f1))
print("F1-Score-macro: {}".format(f2))
print()

devel_result["ner_import_model_file"] = ner_imfile
devel_result["f1_per_class_ner"] = report
devel_result["f1_per_class_ner_space"] = report2
devel_result["Accuracy_ner"] = accuracy
devel_result["F1-Score-weighted_ner"] = f1
devel_result["F1-Score-macro_ner"] = f2


with open(f"{outfile}/devel_result.json", "w", encoding="utf-8") as json_file:
    json.dump(devel_result, json_file, indent=4, ensure_ascii=False)
