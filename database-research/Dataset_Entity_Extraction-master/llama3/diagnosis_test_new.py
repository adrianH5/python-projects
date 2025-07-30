from openai import OpenAI
import json
import re
from tqdm import trange


def test_diagnose(each_diagnosis, true_diagnosis_array, prompt, client):
    # return 'Y'
    chat_return = client.chat.completions.create(
        model="gpt-4o",
        temperature=0.0,
        messages=[
            {"role": "system", "content": "pysician"},
            {
                "role": "user",
                "content": f"{prompt} \n"
                f"Predict Differential Diagnosis: {str(each_diagnosis)}\n"
                f"True Diagnosis: {true_diagnosis_array}",
            },
        ],
    )
    result = chat_return.choices[0].message.content
    # print(each_diagnosis)
    # print(true_diagnosis_array)
    # print(result)
    # exit()
    return result


def acc_top_n(predict_diagnosis, true_diagnosis, Prompt):
    count = 0
    client = OpenAI()

    if len(predict_diagnosis) != len(true_diagnosis):
        print("Number of predicted and true samples not match!")
        return
    # if one predict sample is correct previously, directly skip for larger N.
    skip_index = [0 for i in range(len(predict_diagnosis))]

    for N in range(10):
        for i in trange(len(predict_diagnosis), desc="Steps"):
            # if number of predict diagnosis is less than 10, skip if index exceeds
            if skip_index[i] == 0:
                each_diagnosis = predict_diagnosis[i][N]
                if (
                    each_diagnosis == "Diagnose:"
                    or each_diagnosis == ""
                    or each_diagnosis == "differential diagnosis:"
                ):
                    print("Error")

                # print(each_diagnosis)

                true_diagnosis_array = true_diagnosis[i]

                # print(true_diagnosis_array)
                if len(true_diagnosis_array) != 1:
                    count += 1
                acc = test_diagnose(
                    each_diagnosis, true_diagnosis_array, Prompt, client
                )
                # while acc!='Y' and acc!='N':
                #     print('GPT 4 OUTPUT WRONG RESPONCE! Trying again!')
                #     print(acc)
                #     acc=test_diagnose(each_diagnosis,true_diagnosis_array,Prompt,client)
                acc = acc.split("\n")[0]
                if "Y" in acc:
                    skip_index[i] = 1
                elif "N" not in acc:
                    print(acc)
            else:
                continue

        print("TOP " + str(N + 1) + " ACC: " + str(sum(skip_index) / len(skip_index)))
    return


def read_and_process_jsonl(file_path):
    count = 0
    logit_0_lists = []
    truth_values = []
    input_data = []
    with open(file_path, "r", encoding="utf-8") as file:
        for line in file:
            input_data.append(json.loads(line.strip()))

    for data in input_data:
        split_list = data["target"].split(";")
        split_list = [item.strip() for item in split_list if item.strip()]

        logit_0_content = data["filtered_resps"][0].split("Differential")[-1]
        pattern = r"(\d+)\.\s*([^\d\n]+(?:\n(?!\d+\.)[^\d\n]+)*)"
        diagnosis_list = re.findall(pattern, logit_0_content)
        processed_list = [
            diagnosis.strip()
            for number, diagnosis in diagnosis_list
            if int(number) <= 10
        ]
        if 10 < len(processed_list):
            processed_list = processed_list[:10]

        if len(processed_list) == 10 and len(split_list) == 1:
            truth_values.append(split_list)
            logit_0_lists.append(processed_list)
        else:
            count += 1

    print(count)
    return logit_0_lists, truth_values


prompt1 = """
    Your task is to identify whether the provided predicted differential diagnosis is correct based on the true diagnosis. Carefully review the information and determine the correctness of the prediction. Please notice same diagnosis might be in different words. Only return "Y" for yes or "N" for no, without any other words.
    """

prompt2 = """#Background#
We now have two sets of data, one for real diagnoses and the other for diagnoses predicted by the AI model. We would like you to judge the accuracy of the model's predictions.
#Role#
You are an excellent and experienced Attending Physician who can accurately determine whether the two diagnoses are the same disease.
#Task#
Your task is to identify whether the provided predicted differential diagnosis is correct based on the true diagnosis.
#Constrains#
1. Carefully review the information and determine the correctness of the prediction.
2. Please notice same diagnosis might be in different words.
3. Some of the text given to you is an explanation of the diagnosis. You can use it as an aid to your judgment.
4. When the diagnosis predicted by the model is very close to the true diagnosis, but it is not the same diagnosis, please combine with the explanation of the diagnosis to make a comprehensive judgment
#OutputFormat#
Only return "Y" for yes or "N" for no, without any other words."""

prompt3 = """
# Context
You are an experienced and highly skilled Attending Physician tasked with evaluating the accuracy of diagnostic predictions made by an AI model. 

# Objective
Determine whether the AI model's predicted diagnosis matches the true diagnosis provided.

# Instructions
Fellow the instruction and use step-by-step Inference to make a judgement
1. **Thoroughly review** both the true diagnosis and the AI's predicted diagnosis.
2. **Consider synonymous and related terms**: Recognize that the same disease may be described using different terminology or phrasing.
3. **Utilize provided explanations**: Use your your medical expertise and any additional descriptive information accompanying AI's diagnosis to inform your judgment. 
4. **Assess closely related diagnoses**: If the predicted diagnosis is very similar to the true diagnosis, please relax the criteria a bit and response Y when the AI's diagnosis site and symptoms correspond to the true diagnosis.

# Response Format
Only response with Y or N
- Y, if the AI's predicted diagnosis correctly matches the true diagnosis.
- N, if the AI's predicted diagnosis does not match the true diagnosis.
"""

prompt = prompt3
predict_list, true_list = read_and_process_jsonl(
    "/home/gy237/project/llama3/meta-llama__Meta-Llama-3.1-70B-Instruct_samples_NEJMFinalAll_2024-08-23T12-02-13.267348.jsonl"
)
print(prompt)
acc_top_n(predict_list, true_list, prompt)
