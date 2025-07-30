import pandas as pd
import numpy as np
from tqdm import trange
import torch
from torch.utils.data import TensorDataset, DataLoader, RandomSampler, SequentialSampler
from transformers import BertTokenizer

from tensorflow.keras.preprocessing.sequence import pad_sequences
from sklearn.utils import shuffle
from transformers import BertForTokenClassification, AdamW
from transformers import get_linear_schedule_with_warmup
from seqeval.metrics import f1_score, accuracy_score
import csv
import os
import json
import sys

sys.path.append("../../utilties/")
from add_token import add_tok

MAX_LEN = 128
bs = 4
lr = 1e-5
eps = 1e-8
epochs = 20
max_grad_norm = 1.0
warmup_steps = 500
do_lower_case = False
model_name = "dmis-lab/biobert-v1.1"
add_token = True

_name = model_name.split("/")[-1]
path = f"{_name}_output"
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
    "MAX_LEN": MAX_LEN,
    "optimizer": "AdamW",
    "bs": bs,
    "learning_rate": lr,
    "eps": eps,
    "epochs": epochs,
    "max_grad_norm": max_grad_norm,
    "warmup_steps": warmup_steps,
    "model_name": model_name,
    "BIOES": True,
    "do_lower_case": do_lower_case,
    "special_tokens": True,
    "add_token": add_token,
    "updated_data": True,
    "no_spacy": False,
    "macro": True,
}
with open(f"{path}/hyperparameter.json", "w", encoding="utf-8") as json_file:
    json.dump(hyperparameter, json_file, indent=4, ensure_ascii=False)

# load data
csv_reader = csv.reader(open("../data_updated/train_data_updated.csv"))
train = pd.DataFrame(csv_reader, columns=["word", "label"])

csv_reader = csv.reader(open("../data_updated/test_data_updated.csv"))
test = pd.DataFrame(csv_reader, columns=["word", "label"])


# get list of sentences list
def vet_frases(dataframe):
    sentences = []
    sentences_aux = []
    labels = []
    labels_aux = []
    for word, label in zip(dataframe.word.values, dataframe.label.values):
        sentences_aux.append(word)
        labels_aux.append(label)
        if word == ".":
            sentences.append(sentences_aux)
            labels.append(labels_aux)

            sentences_aux = []
            labels_aux = []
    return sentences, labels


train_sentences, train_labels = vet_frases(train)
test_sentences, test_labels = vet_frases(test)


tokenizer = BertTokenizer.from_pretrained(model_name, do_lower_case=do_lower_case)

if add_token:
    add_tok(train_sentences, train_labels, tokenizer, tokenizer_file)


def tokenize_and_preserve_labels(sentence, text_labels):
    tokenized_sentence = []
    labels = []
    tokenized_sentence.append("[CLS]")
    labels.append("O")
    for word, label in zip(sentence, text_labels):

        # Tokenize the word and count # of subwords the word is broken into
        tokenized_word = tokenizer.tokenize(word)
        n_subwords = len(tokenized_word)

        # Add the tokenized word to the final tokenized word list
        tokenized_sentence.extend(tokenized_word)

        # Add the same label to the new list of labels `n_subwords` times
        # print(label)
        if n_subwords > 1:
            if label.startswith("S-"):
                _label = label.split("-")[1]
                _labels = (
                    [f"B-{_label}"]
                    + [f"I-{_label}"] * (n_subwords - 2)
                    + [f"E-{_label}"]
                )
            elif label.startswith("B-"):
                _label = label.split("-")[1]
                _labels = [f"B-{_label}"] + [f"I-{_label}"] * (n_subwords - 1)
            elif label.startswith("E-"):
                _label = label.split("-")[1]
                _labels = [f"I-{_label}"] * (n_subwords - 1) + [f"E-{_label}"]
            elif label.startswith("I-"):
                _labels = [label] * n_subwords
            elif label == "O":
                _labels = [label] * n_subwords
            else:
                print("Error")
        else:
            _labels = [label] * n_subwords

        labels.extend(_labels)
    tokenized_sentence.append("[SEP]")
    labels.append("O")

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

# to cuda
device = torch.device("cuda" if torch.cuda.is_available() else "cpu")
n_gpu = torch.cuda.device_count()
# print(torch.cuda.get_device_name(0))

# model
model = BertForTokenClassification.from_pretrained(
    model_name,
    num_labels=len(tag2idx),
    output_attentions=False,
    output_hidden_states=False,
)

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
    train_input_ids, train_tags, train_attention_masks, random_state=42
)
val_inputs, val_tags, val_masks = shuffle(
    test_input_ids, test_tags, test_attention_masks, random_state=42
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
        "weight_decay_rate": 0.01,
    },
    {
        "params": [p for n, p in param_optimizer if any(nd in n for nd in no_decay)],
        "weight_decay_rate": 0.0,
    },
]
optimizer = AdamW(optimizer_grouped_parameters, lr=lr, eps=eps)


# Total number of training steps is number of batches * number of epochs.
total_steps = len(train_dataloader) * epochs

# Create the learning rate scheduler.
scheduler = get_linear_schedule_with_warmup(
    optimizer, num_warmup_steps=warmup_steps, num_training_steps=total_steps
)


## Store the average loss after each epoch so we can plot them.
train_loss_values, validation_loss_values = [], []
validation_accuracy, validation_f1 = [], []
best_f1 = 0
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
        # Perform a backward pass to calculate the gradients.
        loss.backward()
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
        if step % 5000 == 0:
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

        if step % 5000 == 0:
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
    accuracy = accuracy_score(valid_tags, pred_tags)
    f1 = f1_score(valid_tags, pred_tags, average="macro")  # macro, weighted
    print("Validation Accuracy: {}".format(accuracy))
    print("Validation F1-Score: {}".format(f1))
    print()
    validation_accuracy.append(accuracy)
    validation_f1.append(f1)
    # print(pred_tags[:100])
    # print(valid_tags[:100])

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

    # save model
    if best_f1 < f1:
        best_f1 = f1
        model.save_pretrained(f"{model_file}/ep_{epoch}_f1_{f1}")

print(f"The best_f1 is {best_f1}")
