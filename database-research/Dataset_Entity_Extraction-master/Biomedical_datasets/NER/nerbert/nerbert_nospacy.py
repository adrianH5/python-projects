# conda create --name bioner python=3.8
# pip install transformers==3.1.0
# pip install seqeval==0.0.12
# pip install tqdm
# torch1.6.0+cu101
# pip install torch==1.13.1+cu117 torchvision==0.14.1+cu117 torchaudio==0.13.1 --extra-index-url https://download.pytorch.org/whl/cu117
# pip install scikit-learn
import pandas as pd
import numpy as np
from tqdm import trange
import torch
from torch.utils.data import TensorDataset, DataLoader, RandomSampler, SequentialSampler
from transformers import BertConfig, BertTokenizerFast
import torch.nn as nn
from tensorflow.keras.preprocessing.sequence import pad_sequences
from sklearn.utils import shuffle
from transformers import BertForTokenClassification, AdamW
from transformers import get_cosine_with_hard_restarts_schedule_with_warmup
from seqeval.metrics import f1_score, accuracy_score
from collections import Counter
from seqeval.metrics import classification_report
import os
import json
import sys
import random

sys.path.append("/home/gy237/project/Biomedical_datasets/utilties/")
from add_token import add_tok

MAX_LEN = 128
# token max length  3/4 : 56, 4/5 : 61, maxium : 435
# addd token max length  3/4 : 58, 4/5 : 63, 5/6 : 66 maxium : 329
bs = 4
SEED = 42
lr = 1e-5
eps = 1e-8
epochs = 14
max_grad_norm = 1.0
warmup_steps = 500
do_lower_case = False
model_name = "dmis-lab/biobert-large-cased-v1.1"
add_token = True
loss_weights = True
no_spacy = True
oversampling = True
weight_decay = 0.1
dropout = False  ## False must
use_fgm = True
smoothing_factor = 0.1
focus_on_dataset = True
# dmis-lab/biobert-v1.1
# dmis-lab/biobert-large-cased-v1.1
# dmis-lab/biobert-large-cased-v1.1-squad
# dmis-lab/biobert-base-cased-v1.2
# dmis-lab/biobert-base-cased-v1.1
# dmis-lab/biobert-base-cased-v1.1-squad
# microsoft/BiomedNLP-PubMedBERT-base-uncased-abstract-fulltext
# microsoft/BiomedNLP-KRISSBERT-PubMed-UMLS-EL
# NeuML/pubmedbert-base-embeddings
# NeuML/pubmedbert-base-embeddings-matryoshka
# bert-base-cased
_name = model_name.split("/")[-1]
path = f"/home/gy237/project/Biomedical_datasets/NER/nerbert/{_name}_output"
if not os.path.exists(path):
    os.makedirs(path)
all_files = os.listdir(path)
time = len(all_files)
path = path + f"/time_{time}"
if os.path.exists(path):
    path += "_1"
    os.makedirs(f"{path}", exist_ok=True)
else:
    os.makedirs(path, exist_ok=True)
train_loss_file = f"{path}/train_loss.csv"
test_loss_file = f"{path}/test_loss.csv"
performance_file = f"{path}/performance.csv"
epoch_loss_file = f"{path}/epoch_loss.csv"
model_file = f"{path}/saved_model"
tokenizer_file = f"{path}/tokenizer_file"
os.makedirs(f"{model_file}", exist_ok=True)


hyperparameter = {
    "time": time,
    "MAX_LEN": MAX_LEN,
    "optimizer": "AdamW",
    "bs": bs,
    "SEED": SEED,
    "learning_rate": lr,
    "eps": eps,
    "epochs": epochs,
    "max_grad_norm": max_grad_norm,
    "warmup_steps": warmup_steps,
    "model_name": model_name,
    "BIOES": "False, use BIO",
    "do_lower_case": do_lower_case,
    "special_tokens": True,
    "add_token": add_token,
    "updated_data": True,
    "no_spacy": no_spacy,
    "loss_weights": loss_weights,
    "oversampling": oversampling,
    "get_cosine_with_hard_restarts_schedule_with_warmup": True,
    "weight_decay": weight_decay,
    "use_fgm": use_fgm,
    "smoothing_factor": smoothing_factor,
    "dropout": dropout,
    "focus_on_dataset": focus_on_dataset,
}
with open(f"{path}/hyperparameter.json", "w", encoding="utf-8") as json_file:
    json.dump(hyperparameter, json_file, indent=4, ensure_ascii=False)

random.seed(SEED)
np.random.seed(SEED)
torch.manual_seed(SEED)
if torch.cuda.is_available():
    torch.cuda.manual_seed_all(SEED)

# config = BertConfig.from_pretrained(model_name,
#                                     hidden_dropout_prob=dropout,
#                                     attention_probs_dropout_prob=dropout)

# load data
if no_spacy:
    with open(
        "/home/gy237/project/Biomedical_datasets/data_update/precessed_data/train_data.json",
        "r",
        encoding="utf-8",
    ) as file:
        train_data = json.load(file)
        # train_data = [ json.load(line) for line in data_list ]
    train_sentences = [i["sen"] for i in train_data]
    train_labels = [i["lab"] for i in train_data]

    with open(
        "/home/gy237/project/Biomedical_datasets/data_update/precessed_data/test_data.json",
        "r",
        encoding="utf-8",
    ) as file:
        test_data = json.load(file)
    test_sentences = [i["sen"] for i in test_data]
    test_labels = [i["lab"] for i in test_data]

else:
    # load data
    with open(
        "/home/gy237/project/Biomedical_datasets/NER/data/train_data.json",
        "r",
        encoding="utf-8",
    ) as file:
        train_data = json.load(file)
        # train_data = [ json.load(line) for line in data_list ]
    train_sentences = [i["sen"] for i in train_data]
    train_labels = [i["lab"] for i in train_data]

    with open(
        "/home/gy237/project/Biomedical_datasets/NER/data/test_data.json",
        "r",
        encoding="utf-8",
    ) as file:
        test_data = json.load(file)
    test_sentences = [i["sen"] for i in test_data]
    test_labels = [i["lab"] for i in test_data]


if focus_on_dataset:
    for i in range(len(train_labels)):
        for j in range(len(train_labels[i])):
            if train_labels[i][j]:
                if train_labels[i][j]["type"] != "Dataset":
                    train_labels[i][j] = False
    for i in range(len(test_labels)):
        for j in range(len(test_labels[i])):
            if test_labels[i][j]:
                if test_labels[i][j]["type"] != "Dataset":
                    test_labels[i][j] = False

label = {}
for i in train_labels:
    for j in i:
        if j:
            if j["type"] in label:
                label[j["type"]] += 1
            else:
                label[j["type"]] = 1

print(label)


if oversampling:
    _train_sentences = []
    _train_labels = []
    for i in range(len(train_labels)):
        flag = False
        count = 2
        for j in range(len(train_labels[i])):
            if train_labels[i][j]:
                flag = True
                if train_labels[i][j]["type"] == "Dataset":
                    count = 3
                if train_labels[i][j]["type"] == "AccessionNumber":
                    count = 4
                if train_labels[i][j]["type"] == "Creator":
                    count = 4
                if train_labels[i][j]["type"] == "URL":
                    count = 15
                if train_labels[i][j]["type"] == "DOI":
                    count = 20
        if flag:
            _train_sentences += [train_sentences[i]] * count
            _train_labels += [train_labels[i]] * count
        else:
            _train_sentences.append(train_sentences[i])
            _train_labels.append(train_labels[i])

    print("After oversampling", len(_train_sentences))
    print("Before oversampling", len(train_labels))
    train_sentences = _train_sentences
    train_labels = _train_labels

# print(test)
# check the label
# print(train_labels[0])


tokenizer = BertTokenizerFast.from_pretrained(model_name, do_lower_case=do_lower_case)

if add_token:
    add_tok(train_sentences, train_labels, tokenizer, tokenizer_file)


def tokenize_and_preserve_labels(sentence, text_labels):
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
    return tokenized_sentence, labels


# process data
train_tokenized_texts_and_labels = [
    tokenize_and_preserve_labels(sent, labs)
    for sent, labs in zip(train_sentences, train_labels)
]
test_tokenized_texts_and_labels = [
    tokenize_and_preserve_labels(sent, labs)
    for sent, labs in zip(test_sentences, test_labels)
]
# print(train_tokenized_texts_and_labels[0])

train_tokenized_texts = [
    token_label_pair[0] for token_label_pair in train_tokenized_texts_and_labels
]
train_labels = [
    token_label_pair[1] for token_label_pair in train_tokenized_texts_and_labels
]
test_tokenized_texts = [
    token_label_pair[0] for token_label_pair in test_tokenized_texts_and_labels
]
test_labels = [
    token_label_pair[1] for token_label_pair in test_tokenized_texts_and_labels
]
# print(train_tokenized_texts[0])


train_input_ids = pad_sequences(
    [tokenizer.convert_tokens_to_ids(txt) for txt in train_tokenized_texts],
    maxlen=MAX_LEN,
    dtype="long",
    value=0.0,
    truncating="post",
    padding="post",
)
test_input_ids = pad_sequences(
    [tokenizer.convert_tokens_to_ids(txt) for txt in test_tokenized_texts],
    maxlen=MAX_LEN,
    dtype="long",
    value=0.0,
    truncating="post",
    padding="post",
)

# tag2idx
_label_list = []
for i in train_labels:
    _label_list += i
tag_values = list(set(_label_list))
tag_values.append("PAD")
# print(sorted(tag_values))
tag2idx = {t: i for i, t in enumerate(tag_values)}
idx2tag = {t: i for i, t in tag2idx.items()}
print(tag2idx)

with open(f"{path}/tag2idx.json", "w", encoding="utf-8") as json_file:
    json.dump(tag2idx, json_file, indent=4, ensure_ascii=False)

print("--------------------------------------------")
# to cuda
device = torch.device("cuda" if torch.cuda.is_available() else "cpu")
torch.manual_seed(SEED)
torch.backends.cudnn.deterministic = True
# print(torch.cuda.get_device_name(0))


if loss_weights:
    _label_list_ = []
    for i in _label_list + ["PAD"] * 100:
        _label_list_.append(tag2idx[i])
    pad_id = tag2idx["PAD"]

    label_counts = Counter(_label_list_)
    total_count = sum(label_counts.values())
    # 计算每个标签的权重（频率的倒数）
    weights = {label: total_count / count for label, count in label_counts.items()}
    for t, v in weights.items():
        weights[t] = np.log1p(v)

    # 引入平滑因子
    smoothing_factor = smoothing_factor
    for t, v in weights.items():
        weights[t] = weights[t] * (1 - smoothing_factor) + smoothing_factor

    m = max(list(weights.values()))
    for t, v in weights.items():
        weights[t] = v / m
    weights[pad_id] = 0.0001
    print(weights)

    # 将权重转换为tensor
    class_weights = torch.tensor(
        [weights[i] for i in range(len(weights))], dtype=torch.float32
    )
    loss_fn = nn.CrossEntropyLoss(weight=class_weights)
    loss_fn = loss_fn.to(device)


if dropout:
    config = BertConfig.from_pretrained(
        model_name,
        num_labels=len(tag2idx),
        attention_probs_dropout_prob=dropout,
        hidden_dropout_prob=dropout,
        output_attentions=False,
        output_hidden_states=False,
    )
else:
    config = BertConfig.from_pretrained(
        model_name,
        num_labels=len(tag2idx),
        output_attentions=False,
        output_hidden_states=False,
    )

# model
model = BertForTokenClassification.from_pretrained(model_name, config=config)

if add_token:
    model.resize_token_embeddings(len(tokenizer))

model.cuda()

train_tags = pad_sequences(
    [[tag2idx.get(l) for l in lab] for lab in train_labels],
    maxlen=MAX_LEN,
    value=tag2idx["PAD"],
    padding="post",
    dtype="long",
    truncating="post",
)
test_tags = pad_sequences(
    [[tag2idx.get(l) for l in lab] for lab in test_labels],
    maxlen=MAX_LEN,
    value=tag2idx["PAD"],
    padding="post",
    dtype="long",
    truncating="post",
)

train_attention_masks = [[float(i != 0.0) for i in ii] for ii in train_input_ids]
test_attention_masks = [[float(i != 0.0) for i in ii] for ii in test_input_ids]

tr_inputs, tr_tags, tr_masks = shuffle(
    train_input_ids, train_tags, train_attention_masks, random_state=SEED
)
val_inputs, val_tags, val_masks = shuffle(
    test_input_ids, test_tags, test_attention_masks, random_state=SEED
)

tr_inputs = torch.tensor(tr_inputs)
val_inputs = torch.tensor(val_inputs)
tr_tags = torch.tensor(tr_tags)
val_tags = torch.tensor(val_tags)
tr_masks = torch.tensor(tr_masks)
val_masks = torch.tensor(val_masks)

train_data = TensorDataset(tr_inputs, tr_masks, tr_tags)
train_sampler = RandomSampler(train_data)
train_dataloader = DataLoader(train_data, sampler=train_sampler, batch_size=bs)

valid_data = TensorDataset(val_inputs, val_masks, val_tags)
valid_sampler = SequentialSampler(valid_data)
valid_dataloader = DataLoader(valid_data, sampler=valid_sampler, batch_size=bs)

print(" ")
print(f"Len of train_dataloader is {len(train_dataloader)}")
print(f"Len of valid_dataloader is {len(valid_dataloader)}")
print(" ")


# optimizer
param_optimizer = list(model.named_parameters())
no_decay = ["bias", "gamma", "beta"]
optimizer_grouped_parameters = [
    {
        "params": [
            p for n, p in param_optimizer if not any(nd in n for nd in no_decay)
        ],
        "weight_decay_rate": weight_decay,
    },
    {
        "params": [p for n, p in param_optimizer if any(nd in n for nd in no_decay)],
        "weight_decay_rate": 0.0,
    },
]
optimizer = AdamW(
    optimizer_grouped_parameters, lr=lr, eps=eps, weight_decay=weight_decay
)


# Total number of training steps is number of batches * number of epochs.
total_steps = len(train_dataloader) * epochs

# Create the learning rate scheduler.
scheduler = get_cosine_with_hard_restarts_schedule_with_warmup(
    optimizer,
    num_warmup_steps=warmup_steps,
    num_training_steps=total_steps,
    num_cycles=epochs // 2,
)

# 对抗训练
if use_fgm:

    class FGM:
        def __init__(self, model):
            self.model = model
            self.backup = {}

        def attack(self, epsilon=1.0, emb_name="emb"):
            for name, param in self.model.named_parameters():
                if param.requires_grad and emb_name in name:
                    self.backup[name] = param.data.clone()
                    norm = torch.norm(param.grad)
                    if norm != 0:
                        r_at = epsilon * param.grad / norm
                        param.data.add_(r_at)

        def restore(self, emb_name="emb"):
            for name, param in self.model.named_parameters():
                if param.requires_grad and emb_name in name:
                    assert name in self.backup
                    param.data = self.backup[name]
            self.backup = {}

    fgm = FGM(model)


## Store the average loss after each epoch so we can plot them.
train_loss_values, validation_loss_values = [], []
validation_accuracy, validation_f1 = [], []
validation_f2 = []
best_f1 = 0
_f1_per_class = {}
for epoch in trange(epochs, desc="Epoch"):
    # Put the model into training mode.
    model.train()
    # Reset the total loss for this epoch.
    train_loss_list = []
    # Training loop
    for step, batch in enumerate(train_dataloader):
        # add batch to gpu
        batch = tuple(t.to(device) for t in batch)
        b_input_ids, b_input_mask, b_labels = batch
        # Always clear any previously calculated gradients before performing a backward pass.
        model.zero_grad()
        # forward pass
        # This will return the loss (rather than the model output)
        # because we have provided the `labels`.
        outputs = model(
            b_input_ids,
            token_type_ids=None,
            attention_mask=b_input_mask,
            labels=b_labels,
        )
        # print(outputs)

        # get the loss
        loss = outputs[0]
        if loss_weights:
            loss = loss_fn(outputs[1].view(-1, outputs[1].size(-1)), b_labels.view(-1))

        # Perform a backward pass to calculate the gradients.
        loss.backward()

        if use_fgm:
            # 对抗训练
            fgm.attack()  # 修改embedding
            # optimizer.zero_grad() # 梯度累加，不累加去掉注释
            outputs = model(
                b_input_ids,
                token_type_ids=None,
                attention_mask=b_input_mask,
                labels=b_labels,
            )
            loss_sum = outputs[0]
            if loss_weights:
                loss_sum = loss_fn(
                    outputs[1].view(-1, outputs[1].size(-1)), b_labels.view(-1)
                )

            loss_sum.backward()  # 累加对抗训练的梯度
            fgm.restore()  # 恢复Embedding的参数

        # Clip the norm of the gradient
        # This is to help prevent the "exploding gradients" problem.
        torch.nn.utils.clip_grad_norm_(
            parameters=model.parameters(), max_norm=max_grad_norm
        )
        # update parameters
        optimizer.step()
        # Update the learning rate.
        scheduler.step()

        # track train loss
        train_loss_list += [loss.mean().item()]
        if step % 2500 == 0:
            train_df = pd.DataFrame({"train_loss": train_loss_list})
            train_df.to_csv(train_loss_file, index=False)

    # Calculate the average loss over the training data.
    avg_train_loss = sum(train_loss_list) / len(train_dataloader)
    print()
    print("Average train loss: {}".format(avg_train_loss))

    # Store the loss value for plotting the learning curve.
    train_loss_values.append(avg_train_loss)

    # Put the model into evaluation mode
    model.eval()
    # Reset the validation loss for this epoch.
    eval_loss = []
    predictions, true_labels = [], []
    for step, batch in enumerate(valid_dataloader):
        batch = tuple(t.to(device) for t in batch)
        b_input_ids, b_input_mask, b_labels = batch

        # Telling the model not to compute or store gradients,
        # saving memory and speeding up validation
        with torch.no_grad():
            # Forward pass, calculate logit predictions.
            # This will return the logits rather than the loss because we have not provided labels.
            outputs = model(
                b_input_ids,
                token_type_ids=None,
                attention_mask=b_input_mask,
                labels=b_labels,
            )
        # Move logits and labels to CPU
        logits = outputs[1].detach().cpu().numpy()
        label_ids = b_labels.to("cpu").numpy()

        # Calculate the accuracy for this batch of test sentences.
        eval_loss += [outputs[0].mean().item()]
        predictions.extend([list(p) for p in np.argmax(logits, axis=2)])
        true_labels.extend(label_ids)

        if step % 500 == 0:
            test_df = pd.DataFrame({"eval_loss": eval_loss})
            test_df.to_csv(test_loss_file, index=False)

    eval_loss = sum(eval_loss) / len(valid_dataloader)
    validation_loss_values.append(eval_loss)
    print("Validation loss: {}".format(eval_loss))

    pred_tags = [
        tag_values[p_i]
        for p, l in zip(predictions, true_labels)
        for p_i, l_i in zip(p, l)
        if tag_values[l_i] != "PAD"
    ]
    valid_tags = [
        tag_values[l_i] for l in true_labels for l_i in l if tag_values[l_i] != "PAD"
    ]

    for i in range(len(valid_tags)):
        valid_tags[i] = valid_tags[i].split("-")[-1]
        pred_tags[i] = pred_tags[i].split("-")[-1]
    report = classification_report(valid_tags, pred_tags, digits=len(idx2tag.keys()))
    print(report)
    _f1_per_class[str(epoch)] = report
    with open(f"{path}/f1_per_class.json", "w", encoding="utf-8") as json_file:
        json.dump(_f1_per_class, json_file, indent=4, ensure_ascii=False)

    accuracy = accuracy_score(valid_tags, pred_tags)
    f1 = f1_score(valid_tags, pred_tags, average="weighted")  # macro, weighted
    f2 = f1_score(valid_tags, pred_tags, average="macro")
    print("Validation Accuracy: {}".format(accuracy))
    print("Validation F1-Score-weighted: {}".format(f1))
    print("Validation F1-Score-macro: {}".format(f2))
    print()
    validation_accuracy.append(accuracy)
    validation_f1.append(f1)
    validation_f2.append(f2)
    # print(pred_tags[:100])
    # print(valid_tags[:100])

    # save something
    performance_df = pd.DataFrame(
        {
            "validation_accuracy": validation_accuracy,
            "validation_f1_weighted": validation_f1,
            "validation_f1_macro": validation_f2,
        }
    )
    performance_df.to_csv(performance_file, index=False)

    epoch_loss_df = pd.DataFrame(
        {
            "train_loss_values": train_loss_values,
            "validation_loss_values": validation_loss_values,
        }
    )
    epoch_loss_df.to_csv(epoch_loss_file, index=False)

    # save model
    if best_f1 < f1:
        best_f1 = f1
        torch.save(model, f"{model_file}/ep_{epoch}_f1_{f1}.pth")

print(f"The best_f1 is {best_f1}")
