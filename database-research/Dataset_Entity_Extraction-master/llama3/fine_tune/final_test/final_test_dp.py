import json
from datasets import load_dataset
from tqdm import trange

# 加载数据
data = load_dataset("YBXL/NEJM_Reasoning_Final_test")

dataset = data["train"]
_query = data["train"]["query"]
answer = data["train"]["answer"]

prompt = [i.split("INPUT:")[0] for i in _query]
query = [i.split("INPUT:")[1] for i in _query]

for i in range(len(prompt) - 1):
    if prompt[i] != prompt[i + 1]:
        print("Error")


import torch
from transformers import AutoTokenizer, AutoModelForCausalLM
from peft import PeftModel, PeftConfig

# 例如: finetune_model_path='FlagAlpha/Llama2-Chinese-7b-Chat-LoRA'

path = "output_lr1e-4/checkpoint-1500"

finetune_model_path = f"/home/gy237/project/llama3/fine_tune/{path}"
config = PeftConfig.from_pretrained(finetune_model_path)

base_model_name_or_path = "meta-llama/Meta-Llama-3-8B-Instruct"
tokenizer = AutoTokenizer.from_pretrained(
    config.base_model_name_or_path, use_fast=False
)

tokenizer.pad_token = tokenizer.eos_token
device_map = "cuda:0" if torch.cuda.is_available() else "auto"
model = AutoModelForCausalLM.from_pretrained(
    config.base_model_name_or_path,
    device_map=device_map,
    torch_dtype=torch.float16,
    load_in_8bit=True,
    trust_remote_code=True,
    use_flash_attention_2=True,
)
model = PeftModel.from_pretrained(model, finetune_model_path, device_map={"": 0})
model = model.eval()

dic_list = []
for i in trange(len(prompt), desc="Step"):
    input_ids = tokenizer(
        [f"<s>Human: {prompt[i] + query[i]}\n</s><s>Assistant: "],
        return_tensors="pt",
        add_special_tokens=False,
    ).input_ids

    if torch.cuda.is_available():
        input_ids = input_ids.to("cuda")
    generate_input = {
        "input_ids": input_ids,
        "max_new_tokens": 512,
        "do_sample": True,
        "top_k": 50,
        "top_p": 0.95,
        "temperature": 0.3,
        "repetition_penalty": 1.3,
        "eos_token_id": tokenizer.eos_token_id,
        "bos_token_id": tokenizer.bos_token_id,
        "pad_token_id": tokenizer.pad_token_id,
    }
    generate_ids = model.generate(**generate_input)
    text = tokenizer.decode(generate_ids[0])

    dic_list.append({"truth": answer[i], "logit_0": text})

json_path = f"/home/gy237/project/llama3/fine_tune/final_test/final_test_{path}.json"

with open(json_path, "w", encoding="utf-8") as file:
    json.dump(dic_list, file, ensure_ascii=False, indent=4)


import sys

sys.path.append("/home/gy237/project/llama3/unsloth/final_test_data/")
from test import *

result = test(json_path)

dct = {f"{path}": result}
with open(
    f"/home/gy237/project/llama3/fine_tune/final_test/final_test_{path}_result.json",
    "w",
    encoding="utf-8",
) as file:
    json.dump(dct, file, ensure_ascii=False, indent=4)
