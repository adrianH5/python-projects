from datasets import load_dataset
import csv

# 文件路径
train_file = "/home/gy237/project/llama3/data/train.csv"
with open(train_file, "w", newline="") as f:
    # 指定CSV写入器，delimiter默认为逗号
    writer = csv.writer(f)
    # 写入表头
    writer.writerow(["text"])

# 加载数据
train = load_dataset("YBXL/diagnosis_train")

# 获取train数据集
train_dataset = train["train"]["conversations"]
# print(train_dataset["conversations"][:1])
for i in range(len(train_dataset)):
    train_list = train_dataset[i]
    question = train_list[0]["content"].replace("\n", " ")
    answer = train_list[1]["content"].replace("\n", " ")
    q_a = "<s>Human: " + question + "\n</s><s>Assistant: " + answer + "\n</s>"

    # 打开文件并创建CSV写入器
    with open(train_file, "a+", newline="") as f:
        # 指定CSV写入器，delimiter默认为逗号
        writer = csv.writer(f)

        # 写入数据
        writer.writerow([q_a])

print(f"数据已写入到 {train_file}")

# "<s>Human: "+问题+"\n</s><s>Assistant: "+答案+"\n"</s>

test_file = "/home/gy237/project/llama3/data/test.csv"
with open(test_file, "w", newline="") as f:
    # 指定CSV写入器，delimiter默认为逗号
    writer = csv.writer(f)
    # 写入表头
    writer.writerow(["text"])

test = load_dataset("YBXL/NEJM_Reasoning_Subset_test")
# print(test)
test_dataset = test["test"]
for i in range(len(test_dataset)):
    question = test["test"]["query"][i]
    answer = test["test"]["answer"][i]
    q_a = "<s>Human: " + question + "\n</s><s>Assistant: " + answer + "\n</s>"

    # 打开文件并创建CSV写入器
    with open(test_file, "a+", newline="") as f:
        # 指定CSV写入器，delimiter默认为逗号
        writer = csv.writer(f)

        # 写入数据
        writer.writerow([q_a])

print(f"数据已写入到 {test_file}")
