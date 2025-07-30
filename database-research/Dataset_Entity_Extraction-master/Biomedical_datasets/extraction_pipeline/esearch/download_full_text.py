import os
import json
import pandas as pd
from nltk.corpus import stopwords
import numpy as np
import csv
import string

# nltk.download('stopwords')
stop_words = list(set(stopwords.words("english")))


def process(word_list):
    word_list_ = []
    for word in word_list:
        word = word.strip(string.punctuation)
        letters_only = [char for char in word if char.isalpha()]
        if word not in stop_words and len(letters_only) > 3:
            word_list_.append(word)
    return word_list_


folder_path = "/home/gy237/project/Biomedical_datasets/extraction_pipeline/esearch/pmcid_sample_gui"
path2 = "/home/gy237/project/Biomedical_datasets/extraction_pipeline/esearch/pmcid_sample_kalpana"
all_items = os.listdir(folder_path)
all_items = [i.split(".")[0] for i in all_items if i.endswith(".txt")]
count = 0
data = []
for name in all_items:
    with open(f"{folder_path}/{name}.txt", "r") as file:
        pmcids = [i.strip() for i in file.readlines()]
    with open(f"{path2}/{name}.txt", "r") as file:
        pmcids.extend([i.strip() for i in file.readlines()])

    # # download the files
    # os.makedirs(f'/home/gy237/project/Biomedical_datasets/extraction_pipeline/esearch/pmcid_full_text_kalpana/{name}', exist_ok=True)

    # for pmcid in pmcids:
    #     os.system(f'''wget -c -O /home/gy237/project/Biomedical_datasets/extraction_pipeline/esearch/pmcid_full_text_kalpana/{name}/{pmcid}.json https://www.ncbi.nlm.nih.gov/research/bionlp/RESTful/pmcoa.cgi/BioC_json/{pmcid}/unicode''')

    # exit()
    # if False:

    papers_dic = []
    papers = []
    corpus = []
    for pmcid in pmcids:
        try:
            with open(
                f"/home/gy237/project/Biomedical_datasets/extraction_pipeline/key_word/{name}/{pmcid}.json",
                "r",
                encoding="utf-8",
            ) as f:
                paper = json.load(f)
                assert len(paper) == 1
                paper = paper[0]
                papers.append(paper)

            dic = {"method": [], "intro": [], "result": [], "data_ava": []}
            passages = paper["documents"][0]["passages"]
            for i in range(len(passages)):
                passage_type = passages[i]["infons"]["section_type"]
                passage_text = passages[i]["text"]
                if "method" in passage_type.lower():
                    corpus.append(passage_text)
                    dic["method"].append(passage_text)
                if "intro" in passage_type.lower():
                    corpus.append(passage_text)
                    dic["intro"].append(passage_text)
                if "result" in passage_type.lower():
                    corpus.append(passage_text)
                    dic["result"].append(passage_text)
                if (
                    "suppl" in passage_type.lower()
                    and "data availability" in passages[i - 1]["text"].lower()
                ):
                    corpus.append(passage_text)
                    dic["data_ava"].append(passage_text)
            papers_dic.append(dic)
        except:
            print(f"This pmcid is not accessible: {pmcid}")
    print(f"{name}: {len(corpus)}")

    words_list = set()
    for doc in corpus:
        words = doc.split(" ")
        words_list = words_list.union(set(words))

    words_set = process(words_list)

    n_docs = len(corpus)  # ·Number of documents in the corpus
    n_words_set = len(words_set)  # ·Number of unique words in the

    df_tf = pd.DataFrame(np.zeros((n_docs, n_words_set)), columns=words_set)

    # Compute Term Frequency (TF)
    for i in range(n_docs):
        words = corpus[i].split(" ")  # Words in the document
        words = process(words)
        for w in words:
            df_tf.loc[i, w] = df_tf.loc[i, w] + (1 / len(words))
    print("TF")
    idf = {}
    for w in words_set:
        k = 0  # number of documents in the corpus that contain this word
        for i in range(n_docs):
            _list = process(corpus[i].split(" "))
            if w in _list:
                k += 1
        idf[w] = np.log2(n_docs / k)
    print("IDF")
    df_tf_idf = df_tf.copy()
    for w in range(len(words_set)):
        word_ = words_set[w]
        for i in range(n_docs):
            df_tf_idf.iloc[i, w] = df_tf.iloc[i, w] * idf[word_]
    print("TF-IDF")
    # print(df_tf_idf)

    # tr_idf_model  = TfidfVectorizer()
    # tf_idf_vector = tr_idf_model.fit_transform(corpus)
    # tf_idf_array = tf_idf_vector.toarray()
    # words_set = tr_idf_model.get_feature_names_out()
    # df_tf_idf = pd.DataFrame(tf_idf_array, columns = words_set)
    # df_name = df_tf_idf.columns
    # for col in df_name:
    #     letters_only = [char for char in col if char.isalpha()]
    #     # print(letters_only)
    #     if col in stop_words or len(letters_only) < 3:
    #         df_tf_idf = df_tf_idf.drop(col, axis=1)

    # print(words_set)
    # print(df_tf_idf)
    name_data = []
    name_list = []
    value_list = []
    words_set = df_tf_idf.columns
    for doc_index in range(df_tf_idf.shape[0]):
        tfidf_vector = df_tf_idf.iloc[doc_index].values
        top_n_indices = np.argsort(tfidf_vector)[-5:][::-1]
        top_n = {}
        for i in top_n_indices:
            top_n_keyword = words_set[i]
            top_n_tf_idf = tfidf_vector[i]
            letters_only = [char for char in top_n_keyword if char.isalpha()]
            if top_n_tf_idf != 0.0:
                if top_n_keyword not in stop_words and len(letters_only) > 3:
                    top_n[top_n_keyword] = top_n_tf_idf
                    name_list.append(top_n_keyword)
                    value_list.append(top_n_tf_idf)

        name_data.append(top_n)

    with open(
        f"/home/gy237/project/Biomedical_datasets/extraction_pipeline/key_word/{name}.tsv",
        "w",
        newline="",
    ) as file:
        tsv_writer = csv.writer(file, delimiter="\t")
        for item1, item2 in zip(name_list, value_list):
            tsv_writer.writerow([item1, item2])

    data.append({"name": name, "data": name_data})

with open(
    "/home/gy237/project/Biomedical_datasets/extraction_pipeline/key_word/test.json",
    "w",
    encoding="utf-8",
) as f:
    json.dump(data, f, ensure_ascii=False, indent=4)
