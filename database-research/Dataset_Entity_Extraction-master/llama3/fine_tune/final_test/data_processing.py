from datasets import load_dataset
import csv


# "<s>Human: "+问题+"\n</s><s>Assistant: "+答案+"\n"</s>

test_file = "/home/gy237/project/llama3/fine_tune/final_test/final_test.csv"
with open(test_file, "w", newline="") as f:
    # 指定CSV写入器，delimiter默认为逗号
    writer = csv.writer(f)
    # 写入表头
    writer.writerow(["text"])

data = load_dataset("YBXL/NEJM_Reasoning_Final_test")
dataset = data["train"]
_query = data["train"]["query"]
answer = data["train"]["answer"]

prompt = [i.split("INPUT:")[0] for i in _query]
query = [i.split("INPUT:")[1] for i in _query]

for i in range(len(prompt) - 1):
    if prompt[i] != prompt[i + 1]:
        print("Error")

for i in range(len(prompt)):

    q_a = (
        "<s>Human: "
        + prompt[i]
        + query[i]
        + "\n</s><s>Assistant: "
        + answer[i]
        + "\n</s>"
    )

    # 打开文件并创建CSV写入器
    with open(test_file, "a+", newline="") as f:
        # 指定CSV写入器，delimiter默认为逗号
        writer = csv.writer(f)

        # 写入数据
        writer.writerow([q_a])

print(f"数据已写入到 {test_file}")
