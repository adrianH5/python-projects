import json
import csv

with open("/home/s211505003/iGEM2/label/combined_label2.csv", "r") as file:
    csv_reader = csv.DictReader(file)

    # 将Python数据写入JSON文件中
    with open(
        "/home/s211505003/iGEM2/fine_tune/data/AdvertiseGen_/row_data.json",
        "wt",
        encoding="utf-8",
    ) as fout:
        system_prompt = "You are an excellent synthetic biologist, especially good at summarizing the functions of synthetic biological components. You are always able to accurately summarize the functions of components and the required chemical and biological environment."
        for row in csv_reader:
            name = row["NAME"]
            file_path = f"/home/s211505003/iGEM2/text_format/BBa_pure/Part^{name}.txt"
            try:
                with open(file_path, "r") as file:
                    text = file.read()
                user_prompt_1 = f'''Please summarize the function of the synthetic biology component named {name} from the provided text. The text is converted from HTML file, and may contain excessive and non-essential information, your task is to provide a clear and concise description focusing on {name}'s functionalities within a six-sentence limit. If the function details are not clear, respond with 'No description of the function.' Here is the text: "{text}"'''
                # user_prompt_1 += f'''The text is as follows: "{text}"'''
                # BEGIN of iad version
                """
                3. I am about to provide a text describing a synthetic biology component named {name} and an associated project where it is utilized. The origin of the content is from HTML source, which could include excessive and non-essential information. Your task is to carefully process this text to eliminate any superfluous content and concentrate solely on detailing the specific functions of {name}. Ensure that you maintain the necessary technical vocabulary and articulate {name}'s functionalities clearly and succinctly. Your summary should be comprehensive yet concise, confined to no more than six sentences. Focus on including all crucial details about the component's features and applications, avoiding any irrelevant information. If the function details are unidentifiable, please respond with 'No description of the function.'.
                    
                4. Please summarize the function of the synthetic biology component named {name} from the provided text. The text is converted from HTML file, and may contain excessive and non-essential information, your task is to provide a clear and concise description focusing on {name}'s functionalities within a six-sentence limit. If the function details are not clear, respond with 'No description of the function.' Here is the text: "{text}"
                """
                # END of iad version
                assistant_response_1 = row["OUTPUT"]
                user_prompt_2 = "Please provide a detailed summary of the necessary environments for the use of this component, focusing on the strains employed. Describe the essential settings, conditions, and biological systems required for its effective use, especially any unique environmental parameters and relevant microbial or genetic strains. If information on the environment or strains is insufficient, respond with 'No description of the environment.'"
                # BEGIN of iad version
                """
                3. Please assist in providing a succinct summary of the different environments necessary for the utilization of this component. It is crucial to include detailed descriptions focusing specifically on the strains that are employed with this component. Use precise and professional terminology to describe the settings, conditions, and biological systems relevant for this component's effective use. Address any unique environment parameters, particularly emphasizing microbial or genetic strains that are integral to the operation of this component. Should there be insufficient information to determine the environment or if specific environments related to essential strains are lacking, please respond with 'No description of the environment.'.
                
                4. Please provide a detailed summary of the necessary environments for the use of this component, focusing on the strains employed. Describe the essential settings, conditions, and biological systems required for its effective use, especially any unique environmental parameters and relevant microbial or genetic strains. If information on the environment or strains is insufficient, respond with 'No description of the environment.'
                """
                # END of iad version
                if row["ENVIRONMENT"]:
                    assistant_response_2 = row["ENVIRONMENT"]
                else:
                    assistant_response_2 = "No description of the environment"

                sample = {
                    "conversations": [
                        {"role": "system", "content": system_prompt},
                        {"role": "user", "content": user_prompt_1},
                        {"role": "assistant", "content": assistant_response_1},
                        {"role": "user", "content": user_prompt_2},
                        {"role": "assistant", "content": assistant_response_2},
                    ]
                }
                fout.write(json.dumps(sample, ensure_ascii=False) + "\n")

            except:
                print(name)
                with open(
                    "/home/s211505003/iGEM2/fine_tune/data/AdvertiseGen_/No_exit_BBa.txt",
                    "a",
                ) as f:
                    f.write(name + "\n")
# 划分成两个json
with open(
    "/home/s211505003/iGEM2/fine_tune/data/AdvertiseGen_/row_data.json",
    "r",
    encoding="utf-8",
) as fin:
    i = 0
    for line in fin:
        dct = json.loads(line)
        i += 1
        if i <= 20:
            with open(
                "/home/s211505003/iGEM2/fine_tune/data/AdvertiseGen_/dev.json",
                "at",
                encoding="utf-8",
            ) as fout:
                fout.write(json.dumps(dct, ensure_ascii=False) + "\n")
        else:
            with open(
                "/home/s211505003/iGEM2/fine_tune/data/AdvertiseGen_/train.json",
                "at",
                encoding="utf-8",
            ) as fout:
                fout.write(json.dumps(dct, ensure_ascii=False) + "\n")
