import pandas as pd
from transformers import BertTokenizer

import csv


# import matplotlib.pyplot as plt
# import seaborn as sns

model_name = "dmis-lab/biobert-v1.1"

# load data
csv_reader = csv.reader(
    open("/home/gy237/project/Biomedical_datasets/NER/data/train_data.csv")
)
train = pd.DataFrame(csv_reader, columns=["word", "label"])

csv_reader = csv.reader(
    open("/home/gy237/project/Biomedical_datasets/NER/data/test_data.csv")
)
test = pd.DataFrame(csv_reader, columns=["word", "label"])


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

tokenizer = BertTokenizer.from_pretrained(model_name, do_lower_case=False)


def tokenize_and_preserve_labels(sentence, text_labels):
    tokenized_sentence = []
    labels = []
    for word, label in zip(sentence, text_labels):

        # Tokenize the word and count # of subwords the word is broken into
        tokenized_word = tokenizer.tokenize(word)
        n_subwords = len(tokenized_word)

        # Add the tokenized word to the final tokenized word list
        tokenized_sentence.extend(tokenized_word)

        # Add the same label to the new list of labels `n_subwords` times
        labels.extend([label] * n_subwords)

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
print(train_tokenized_texts[:2])
print(len(train_tokenized_texts))  # 7020
print(len(train_labels))  # 7020
print(len(test_tokenized_texts))  # 2246
print(len(test_labels))  # 2246

len_list = []
maxium = 0
for i in train_tokenized_texts + test_tokenized_texts:
    _len = len(i)
    len_list += [_len]
    if maxium < _len:
        maxium = _len

print(sorted(len_list)[int(len(len_list) * 4 / 5)])  # 3/4 : 56, 4/5 : 61
print(maxium)  # 435
