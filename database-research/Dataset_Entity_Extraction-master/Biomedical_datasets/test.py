# import torch
# from transformers import BertTokenizer, BertConfig, AutoTokenizer, BertTokenizerFast
# import transformers
# from transformers import BertForTokenClassification


# model_name = 'dmis-lab/biobert-v1.1'
# tokenizer_file = '/home/gy237/project/Biomedical_datasets/utilties/qqdw'
# do_lower_case = True

# tokenizer = BertTokenizerFast.from_pretrained(model_name, do_lower_case=do_lower_case)

# num_added_tokens = tokenizer.add_tokens(['COVID', 'COSICO'])
# tokenizer.save_pretrained(tokenizer_file)
# print('---------------------------------------------')
# print(f"Number of tokens added: {num_added_tokens}")

# vocab_size = len(tokenizer)
# print(f"Vocabulary size: {vocab_size}")

# # model
# model = BertForTokenClassification.from_pretrained(
#     model_name,
#     num_labels=22
# )

# model.resize_token_embeddings(len(tokenizer))

# # 获取词嵌入层
# embedding_layer = model.bert.embeddings.word_embeddings

# # 检查词嵌入矩阵的大小
# print(embedding_layer.weight.size())

# torch.save(model, f'{tokenizer_file}/complete_model.pth')
# # tokenizer.save_pretrained(f"/home/gy237/project/Biomedical_datasets/utilties/qqdw")


# r_tokenizer = BertTokenizerFast.from_pretrained(tokenizer_file, do_lower_case=do_lower_case)

# vocab_size = len(r_tokenizer)
# print(f"Vocabulary size: {vocab_size}")


# model = torch.load(f'{tokenizer_file}/complete_model.pth')

# model = BertForTokenClassification.from_pretrained(
#     tokenizer_file,
#     config=config
# )

# import requests
# def download_epmc_datalinks(pmc_id):
#     base_url = 'https://eutils.ncbi.nlm.nih.gov/entrez/eutils/efetch.fcgi'
#     # base_url = 'https://www.ebi.ac.uk/europepmc/webservices/rest'

#     # Parameters for the request
#     params = {
#         'source': 'PMC',
#         'id': pmc_id,
#         'retmode': 'xml'
#     }

#     response = requests.get(base_url, params=params)
#     print(response.text)

# download_epmc_datalinks('PMC11168932')

# import json
# from datasets import load_dataset
# ds1 = load_dataset("YBXL/NEJM_Reasoning_Final_NEW_PROMPT_test", cache_dir='/home/gy237/project/download_data')
# id1 = ds1['train']['id']
# inpt1 = [ i.split('INPUT:')[-1] for i in ds1['train']['query'] ]
# oupt1 = ds1['train']['answer']
# upload_data1 = []
# for i in range(len(id1)):
#     upload_data1.append({'id': id1[i], 'query' : inpt1[i], 'answer': oupt1[i]})
# print(len(id1))
# print(len(upload_data1))
# with open(f'/home/gy237/project/llama3/new_data/NEJM_Reasoning_Final_NEW_PROMPT_test.json', 'w', encoding='utf-8') as file:
#     json.dump(upload_data1, file, ensure_ascii=False, indent=4)

# NEJM_Reasoning_Final_NEW_PROMPT13
# NEJM_Reasoning_Final_NEW_PROMPT31
# NEJM_Reasoning_Final_NEW_PROMPT45
# NEJM_Reasoning_Final_NEW_PROMPT53
# NEJM_Reasoning_Final_NEW_PROMPT59
# NEJM_Reasoning_Final_NEW_PROMPT64
# NEJM_Reasoning_Final_NEW_PROMPT78
# NEJM_Reasoning_Final_NEW_PROMPT84
# NEJM_Reasoning_Final_NEW_PROMPT95
# NEJM_Reasoning_Final_NEW_PROMPT99
# NEJM_Reasoning_Final_NEW_PROMPT102.  answer特别长
# NEJM_Reasoning_Final_NEW_PROMPT107
# NEJM_Reasoning_Final_NEW_PROMPT118
# NEJM_Reasoning_Final_NEW_PROMPT128
# NEJM_Reasoning_Final_NEW_PROMPT130
# NEJM_Reasoning_Final_NEW_PROMPT131
# NEJM_Reasoning_Final_NEW_PROMPT138
# NEJM_Reasoning_Final_NEW_PROMPT146
# NEJM_Reasoning_Final_NEW_PROMPT147
# NEJM_Reasoning_Final_NEW_PROMPT150
# NEJM_Reasoning_Final_NEW_PROMPT153
# NEJM_Reasoning_Final_NEW_PROMPT154   重复，删除
# NEJM_Reasoning_Final_NEW_PROMPT159
# NEJM_Reasoning_Final_NEW_PROMPT164
# NEJM_Reasoning_Final_NEW_PROMPT169
# NEJM_Reasoning_Final_NEW_PROMPT172
# NEJM_Reasoning_Final_NEW_PROMPT173
# NEJM_Reasoning_Final_NEW_PROMPT179
# NEJM_Reasoning_Final_NEW_PROMPT182
# NEJM_Reasoning_Final_NEW_PROMPT186
# NEJM_Reasoning_Final_NEW_PROMPT194
# NEJM_Reasoning_Final_NEW_PROMPT198
# NEJM_Reasoning_Final_NEW_PROMPT210
# NEJM_Reasoning_Final_NEW_PROMPT213
# NEJM_Reasoning_Final_NEW_PROMPT247
# NEJM_Reasoning_Final_NEW_PROMPT252
# NEJM_Reasoning_Final_NEW_PROMPT262
# NEJM_Reasoning_Final_NEW_PROMPT270
# NEJM_Reasoning_Final_NEW_PROMPT277
# NEJM_Reasoning_Final_NEW_PROMPT281
# NEJM_Reasoning_Final_NEW_PROMPT282
# NEJM_Reasoning_Final_NEW_PROMPT296
# NEJM_Reasoning_Final_NEW_PROMPT299
# NEJM_Reasoning_Final_NEW_PROMPT300
# NEJM_Reasoning_Final_NEW_PROMPT301
# 搞一下血压

# 2021. NCBI Sequence Read Archive. SRP296025


# import json
# import re
# from datasets import load_dataset
# with open('/home/gy237/project/llama3/new_data/NEJM.json', 'r', encoding='utf-8') as file:
#     output = json.load(file)

# ds1 = load_dataset("YBXL/NEJM_Reasoning_Final_NEW_PROMPT_test", cache_dir='/home/gy237/project/download_data')
# id1 = ds1['train']['id']
# prompt = [ i.split('INPUT:')[0] for i in ds1['train']['query'] ]

# upload_data1 = []
# for i in output:
#     query = i['query'].split(' ')
#     for j in range(len(query)-1):
#         if query[j] == 'mm' and  query[j+1][:2] == 'Hg':
#             if len(query[j-1]) >3 :
#                 query[j-1] = query[j-1][:-2] + '/' + query[j-1][-2:]
#                 # print(query[j-1])
#                 # exit()
#     query_ = ' '.join(query)
#     for t in range(len(id1)):
#         if id1[t] == i['id']:
#             inpt = 'INPUT:'.join([prompt[t], query_])
#     upload_data1.append({'id': i['id'], 'query' : inpt, 'answer': i['answer']})
# print(len(output))
# print(len(upload_data1))
# with open(f'/home/gy237/project/llama3/new_data/NEJM_Reasoning_Final_NEW_PROMPT_test.json', 'w', encoding='utf-8') as file:
#     json.dump(upload_data1, file, ensure_ascii=False, indent=4)

import time

count = 0
while True:
    print(count, end=" ")
    time.sleep(6)
    count += 1
