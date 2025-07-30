import numpy as np
import pandas as pd
from itertools import product
import torch
from tqdm import trange
from transformers import BertForSequenceClassification, AdamW, BertTokenizerFast
from torch.utils.data import TensorDataset, DataLoader, RandomSampler, SequentialSampler
from transformers import get_cosine_with_hard_restarts_schedule_with_warmup
from sklearn.utils import shuffle
from sklearn.metrics import accuracy_score, f1_score
import os
import json
import torch.nn as nn
from collections import Counter
import sys

sys.path.append("../utilties/")
from add_token import add_tok
import random

maxlen = 128
SEED = 42
epochs = 14
lr = 1e-5
eps = 1e-8
bs = 4
optimizer = AdamW
do_lower_case = False
num_warmup_steps = 500
max_grad_norm = 1.0
add_token = False
loss_weights = True
oversampling = True
model_name = "dmis-lab/biobert-large-cased-v1.1"


_name = model_name.split("/")[-1]
path = f"{_name}_output"
if not os.path.exists(path):
    os.makedirs(path)
all_files = os.listdir(path)
time = len(all_files)
path = path + f"/time_{time}"
os.makedirs(path, exist_ok=True)
train_loss_file = f"{path}/train_loss.csv"
test_loss_file = f"{path}/test_loss.csv"
performance_file = f"{path}/performance.csv"
epoch_loss_file = f"{path}/epoch_loss.csv"
model_file = f"{path}/saved_model"
tokenizer_file = f"{path}/tokenizer_file"

hyperparameter = {
    "time": time,
    "MAX_LEN": maxlen,
    "optimizer": str(optimizer),
    "batch_size": bs,
    "learning_rate": lr,
    "eps": eps,
    "epochs": epochs,
    "max_grad_norm": max_grad_norm,
    "warmup_steps": num_warmup_steps,
    "model_name": model_name,
    "do_lower_case": do_lower_case,
    "Seed": SEED,
    "special_tokens": True,
    "get_linear_schedule_with_warmup": False,
    "get_cosine_with_hard_restarts_schedule_with_warmup": "True and cycle = epochs//2",
    "add_token": add_token,
    "updated_data": True,
    "loss_weights": loss_weights,
    "oversampling": oversampling,
}
with open(f"{path}/hyperparameter.json", "w", encoding="utf-8") as json_file:
    json.dump(hyperparameter, json_file, indent=4, ensure_ascii=False)

random.seed(SEED)
np.random.seed(SEED)
torch.manual_seed(SEED)
if torch.cuda.is_available():
    torch.cuda.manual_seed_all(SEED)


with open(
    "../../data_update/precessed_data/train_data.json", "r", encoding="utf-8"
) as file:
    train_data = json.load(file)
train_sen = [i["sen"] for i in train_data]
train_lab = [i["lab"] for i in train_data]
train_rel = [i["rel"] for i in train_data]

with open(
    "../../data_update/precessed_data/test_data.json", "r", encoding="utf-8"
) as file:
    test_data = json.load(file)
test_sen = [i["sen"] for i in test_data]
test_lab = [i["lab"] for i in test_data]
test_rel = [i["rel"] for i in test_data]


tokenizer = BertTokenizerFast.from_pretrained(model_name, do_lower_case=do_lower_case)

if add_token:
    add_tok(train_sen, train_lab, tokenizer, tokenizer_file)


# add special @$ and classify data
def add_t(sen, lab, rel):
    _sen = []
    _bool = []
    for i in range(len(sen)):
        for j in range(len(lab[i])):
            if lab[i][j]:
                if sen[i][j] != lab[i][j]["name"]:
                    print("error")
                # sen[i][j] = '@' + sen[i][j] + '$'

        # select the direction
        rel_id = []
        for k in range(len(rel[i])):
            if rel[i][k] != "No Relation":
                rel_id.append((rel[i][k]["head"], rel[i][k]["end"]))

        entities_s = [
            j["id"]
            for j in lab[i]
            if j and j["type"] in ["Dataset", "Repository", "Creator"]
        ]
        entities_e = [
            j["id"]
            for j in lab[i]
            if j and j["type"] in ["URL", "AccessionNumber", "DOI"]
        ]

        if entities_s == [] or entities_e == []:
            _bool.append(0)
            _sen.append(sen[i])
        else:
            com_list = list(product(entities_s, entities_e))
            for j in range(len(com_list)):
                # _bool
                _n = False
                for n in rel_id:
                    if set([com_list[j][0], com_list[j][1]]) == set(n):
                        if _n == True:
                            print("erroe")
                        _n = True
                if _n:
                    _bool.append(1)
                else:
                    _bool.append(0)

                # add @
                flag = 0
                _sen_ = sen[i]
                for m in range(len(lab[i])):
                    # put @ on the selected com
                    if lab[i][m] and lab[i][m]["id"] in com_list[j]:
                        _sen_ = _sen_[:m] + ["@" + _sen_[m] + "$"] + _sen_[m + 1 :]
                        flag += 1
                _sen.append(_sen_)
                if flag != 2:
                    print("error")

    return _sen, _bool


train_sen, train_bool = add_t(train_sen, train_lab, train_rel)
test_sen, test_bool = add_t(test_sen, test_lab, test_rel)

train_sen_ = []
for i in train_sen:
    train_sen_.append("".join(i))
test_sen_ = []
for i in test_sen:
    test_sen_.append("".join(i))


if oversampling:
    _train_sen = []
    _train_bool = []
    for i in range(len(train_bool)):
        if train_bool[i] == 0:
            _train_sen.append(train_sen_[i])
            _train_bool.append(train_bool[i])
        else:
            _train_sen.extend([train_sen_[i]] * 3)
            _train_bool.extend([train_bool[i]] * 3)
    train_sen_ = _train_sen
    train_bool = _train_bool


label = {}
for i in train_bool:
    if i in label.keys():
        label[i] += 1
    else:
        label[i] = 1
print(label)


device = torch.device("cuda")
torch.manual_seed(SEED)
torch.backends.cudnn.deterministic = True


# load dataset
def load_data(sentences, labels, tokenizer, maxlen):
    input_ids = []
    attention_masks = []
    for sent in sentences:
        encoded_dict = tokenizer.encode_plus(
            sent,
            add_special_tokens=True,
            max_length=maxlen,
            padding="max_length",
            truncation=True,
            return_attention_mask=True,
            return_tensors="pt",
        )

        input_ids.append(encoded_dict["input_ids"])
        attention_masks.append(encoded_dict["attention_mask"])

    # convert lists into tensors
    input_ids = torch.cat(input_ids, dim=0)
    attention_masks = torch.cat(attention_masks, dim=0)
    labels_tensor = torch.tensor(labels)

    dataset = TensorDataset(input_ids, attention_masks, labels_tensor)

    return dataset


model = BertForSequenceClassification.from_pretrained(
    model_name, num_labels=2, output_attentions=False, output_hidden_states=False
)

if add_token:
    model.resize_token_embeddings(len(tokenizer))

model.cuda()

train_sen_, train_bool = shuffle(train_sen_, train_bool, random_state=SEED)
test_sen_, test_bool = shuffle(test_sen_, test_bool, random_state=SEED)


train_data = load_data(train_sen_, train_bool, tokenizer=tokenizer, maxlen=maxlen)
test_data = load_data(test_sen_, test_bool, tokenizer=tokenizer, maxlen=maxlen)

if loss_weights:
    label_counts = Counter(train_bool)
    total_count = sum(label_counts.values())
    # 计算每个标签的权重（频率的倒数）
    weights = {label: total_count / count for label, count in label_counts.items()}

    for t, v in weights.items():
        weights[t] = np.log1p(v)
    m = max(list(weights.values()))
    for t, v in weights.items():
        weights[t] = v / m
    print(weights)
    # 将权重转换为tensor
    class_weights = torch.tensor(
        [weights[i] for i in range(len(weights))], dtype=torch.float32
    )
    loss_fn = nn.CrossEntropyLoss(weight=class_weights)
    loss_fn = loss_fn.to(device)


train_dataloader = DataLoader(
    train_data, sampler=RandomSampler(train_data), batch_size=bs
)

val_dataloader = DataLoader(
    test_data, sampler=SequentialSampler(test_data), batch_size=bs
)
print(" ")
print(f"Len of train_dataloader is {len(train_dataloader)}")
print(f"Len of valid_dataloader is {len(val_dataloader)}")
print(" ")

optim = optimizer(model.parameters(), lr=lr, eps=eps)

# scheduler = get_linear_schedule_with_warmup(
#             optim,
#             num_warmup_steps=num_warmup_steps,
#             num_training_steps=len(train_dataloader) * epochs
#         )
scheduler = get_cosine_with_hard_restarts_schedule_with_warmup(
    optim,
    num_warmup_steps=num_warmup_steps,
    num_training_steps=len(train_dataloader) * epochs,
    num_cycles=epochs // 2,
)


train_loss_values, validation_loss_values = [], []
validation_accuracy, validation_f1 = [], []
best_f1 = 0
for epoch in trange(epochs, desc="Epoch"):
    train_loss_list = []
    model.train()
    for step, batch in enumerate(train_dataloader):
        b_input_ids = batch[0].to(device)
        b_input_mask = batch[1].to(device)
        b_labels = batch[2].to(device)

        model.zero_grad()
        output = model(
            b_input_ids,
            token_type_ids=None,
            attention_mask=b_input_mask,
            labels=b_labels,
        )
        loss = output[0]
        if loss_weights:
            loss = loss_fn(output[1].view(-1, output[1].size(-1)), b_labels)
        loss.backward()
        torch.nn.utils.clip_grad_norm_(model.parameters(), max_grad_norm)
        optim.step()
        scheduler.step()

        train_loss_list += [loss.mean().item()]
        if step % 5000 == 0:
            train_df = pd.DataFrame({"train_loss": train_loss_list})
            train_df.to_csv(train_loss_file, index=False)

    avg_train_loss = sum(train_loss_list) / len(train_dataloader)
    train_loss_values.append(avg_train_loss)
    print("average training loss for epoch: {}".format(avg_train_loss))

    # validation
    eval_loss = []
    predictions, true_labels = [], []
    model.eval()
    for step, batch in enumerate(val_dataloader):
        b_input_ids = batch[0].to(device)
        b_attention_mask = batch[1].to(device)
        b_labels = batch[2].to(device)

        with torch.no_grad():
            output = model(
                b_input_ids,
                token_type_ids=None,
                attention_mask=b_attention_mask,
                labels=b_labels,
            )

        loss = output[0]
        preds = output[1].detach().cpu().numpy()
        labels = b_labels.to("cpu").numpy()
        preds = np.argmax(preds, axis=1)

        eval_loss += [output[0].mean().item()]
        predictions.extend(preds)
        true_labels.extend(labels)
        if step % 5000 == 0:
            test_df = pd.DataFrame({"eval_loss": eval_loss})
            test_df.to_csv(test_loss_file, index=False)

    avg_val_loss = sum(eval_loss) / len(val_dataloader)
    validation_loss_values.append(avg_val_loss)
    print("average validation loss for epoch: {}".format(avg_val_loss))

    accuracy = accuracy_score(true_labels, predictions)
    f1 = f1_score(true_labels, predictions, average="weighted")
    print("Validation Accuracy: {}".format(accuracy))
    print("Validation F1-Score: {}".format(f1))
    validation_accuracy.append(accuracy)
    validation_f1.append(f1)

    # save something
    performance_df = pd.DataFrame(
        {"validation_accuracy": validation_accuracy, "validation_f1": validation_f1}
    )
    performance_df.to_csv(performance_file, index=False)

    epoch_loss_df = pd.DataFrame(
        {
            "train_loss_values": train_loss_values,
            "validation_loss_values": validation_loss_values,
        }
    )
    epoch_loss_df.to_csv(epoch_loss_file, index=False)

    if best_f1 < f1:
        best_f1 = f1
        model.save_pretrained(f"{model_file}/ep_{epoch}_f1_{f1}")

print(f"The best_f1 is {best_f1}")
