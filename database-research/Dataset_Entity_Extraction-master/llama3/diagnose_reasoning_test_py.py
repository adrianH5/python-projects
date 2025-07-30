from openai import OpenAI
import json
import re


def test_diagnose(each_diagnosis, true_diagnosis_array, prompt, client):
    chat_return = client.chat.completions.create(
        model="gpt-4o",
        messages=[
            {"role": "system", "content": "pysician"},
            {
                "role": "user",
                "content": f"{prompt} \n"
                f"Predict Diagnosis: str({each_diagnosis})\n"
                f"True Differential Diagnosis: {true_diagnosis_array}",
            },
        ],
    )
    result = chat_return.choices[0].message.content
    return result


def acc_top_n(predict_diagnosis, true_diagnosis):
    # change for your environment
    # api_key=os.environ.get("OPENAI_API_KEY")
    client = OpenAI()

    Prompt = """
    As an experienced pysician, your task is to identify whether the provided predicted diagnosis is in the true differential diagnosis. 
    Please notice same diagnosis might be in different words. Only rerutn "Y" for yes or "N" for no. 
    """

    if len(predict_diagnosis) != len(true_diagnosis):
        print("Number of predicted and true samples not match!")
        return
    # if one predict sample is correct previously, directly skip for larger N.
    skip_index = [0 for i in range(len(predict_diagnosis))]

    for N in range(10):
        for i in range(len(predict_diagnosis)):
            # if number of predict diagnosis is less than 10, skip if index exceeds
            if skip_index[i] == 0:
                try:
                    each_diagnosis = predict_diagnosis[i][N]
                    if (
                        each_diagnosis == "Diagnose:"
                        or each_diagnosis == ""
                        or each_diagnosis == "differential diagnosis:"
                    ):
                        each_diagnosis = each_diagnosis + str(i)
                        # print(each_diagnosis)
                except Exception:
                    continue

                # print(each_diagnosis)

                true_diagnosis_array = true_diagnosis[i]

                # print(true_diagnosis_array)
                acc = test_diagnose(
                    each_diagnosis, true_diagnosis_array, Prompt, client
                )
                while acc != "Y" and acc != "N":
                    print("GPT 4 OUTPUT WRONG RESPONCE! Trying again!")
                    print(acc)
                    acc = test_diagnose(
                        each_diagnosis, true_diagnosis_array, Prompt, client
                    )
                if acc == "Y":
                    skip_index[i] = 1
            else:
                continue

        print("TOP " + str(N + 1) + " ACC: " + str(sum(skip_index) / len(skip_index)))
    return


def read_and_process_jsonl(file_path):
    logit_0_lists = []
    truth_values = []
    input_data = []
    with open(file_path, "r", encoding="utf-8") as file:
        for line in file:
            input_data.append(json.loads(line))

    for data in input_data:
        split_list = data["doc"]["answer"].split(";")
        split_list = [item.strip() for item in split_list if item.strip()]
        logit_0_content = data["filtered_resps"][0]
        logit_0_content = logit_0_content.split("Differential")[-1]
        if re.search(r"\d+\.", logit_0_content):
            truth_values.append(split_list)
            # print(split_list)

            pattern = r"(\d+)\.\s*([^,.\d]+(?:\s+(?!\d+\.)[^,.\d]+)*)"
            diagnosis_list = re.findall(pattern, logit_0_content)
            processed_list = [
                diagnosis.strip()
                for number, diagnosis in diagnosis_list
                if int(number) <= 10
            ][:10]
            # print(processed_list)
            # exit()

            logit_0_lists.append(processed_list)
    return logit_0_lists, truth_values


predict_list, true_list = read_and_process_jsonl(
    "/home/gy237/project/llama3/unsloth/meta-llama__Meta-Llama-3.1-70B-Instruct_samples_NEJMFinalAll_2024-08-23T12-02-13.267348.jsonl"
)
# print(predict_list[:2])
# print(true_list[:2])
# exit()
acc_top_n(predict_list, true_list)

# pre = '''
# Differential diagnosis:
# 1. Amyotrophic Lateral Sclerosis (ALS)
# 2. Progressive Supranuclear Palsy (PSP)
# 3. Multiple System Atrophy (MSA)
# 4. Obstructive Sleep Apnea (OSA)
# 5. REM Sleep Behavior Disorder (RBD)
# 6. Vascular Dementia
# 7. Chronic Hypoxemic Encephalopathy
# 8. Cervical Spondylotic Myelopathy
# 9. Degenerative Disc Disease
# 10. Normal Pressure Hydrocephalus
# '''

# tru = 'Regional myocarditis due to infection with Listeria monocytogenes.'

# Prompt="""
#     As an experienced pysician, your task is to identify whether the provided predicted diagnosis is in the true differential diagnosis.
#     Please notice same diagnosis might be in different words. Only rerutn "Y" for yes or "N" for no.
#     """
# client = OpenAI()

# pre_list = pre.split('\n')
# for i in pre_list:
#     acc=test_diagnose(i,tru,Prompt,client)
#     print(acc)
