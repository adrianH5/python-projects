import re

for i in ["train", "dev"]:
    # 打开并读取文本文件
    with open(
        f"/home/s211505003/iGEM2/fine_tune/data/AdvertiseGen_/{i}.json",
        "r",
        encoding="utf-8",
    ) as file:
        text = file.read()

    # 移除所有文本形式的转义字符，但保留换行符 \n 作为文本
    # 这里我们不直接替换掉 \n，而是临时替换为一个占位符，稍后会还原
    text = re.sub(r"\n", "NEWLINE_PLACEHOLDER", text)

    # 使用正则表达式移除所有控制字符（除了换行符 \n）
    # 这里的 \x00-\x1F\x7F-\x9F 范围包括大部分控制字符
    text = re.sub(r"[\x00-\x1F\x7F-\x9F]", "<UNK>", text)

    # 现在移除剩余的所有以文本形式存储的转义字符
    text = re.sub(r"\\.", "<UNK>", text)

    # 还原文本中的换行符占位符
    text = text.replace("NEWLINE_PLACEHOLDER", "\n")

    # 将清理后的文本保存回文件
    with open(
        f"/home/s211505003/iGEM2/fine_tune/data/Cleared/{i}.json", "w", encoding="utf-8"
    ) as file:
        file.write(text)

    print("已清理不可见字符和文本形式的转义字符，并保存到 example_cleaned.txt")
