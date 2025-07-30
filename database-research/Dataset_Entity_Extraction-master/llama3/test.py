# 下载模型
"""import transformers
import torch

model_id = "meta-llama/Meta-Llama-3-8B"

pipeline = transformers.pipeline(
    "text-generation", model=model_id, model_kwargs={"torch_dtype": torch.bfloat16}, device_map="auto"
)
pipeline("Hey how are you doing today?")"""
# # Load model directly
# from transformers import AutoTokenizer, AutoModelForCausalLM

# tokenizer = AutoTokenizer.from_pretrained("meta-llama/Meta-Llama-3-8B-Instruct")
# model = AutoModelForCausalLM.from_pretrained("meta-llama/Meta-Llama-3-8B-Instruct")

# 运行一下看看
"""import torch
from transformers import AutoTokenizer, AutoModelForCausalLM
device_map = "cuda:0" if torch.cuda.is_available() else "auto"
model = AutoModelForCausalLM.from_pretrained('meta-llama/Meta-Llama-3-8B-Instruct',device_map=device_map,torch_dtype=torch.float16,load_in_8bit=True,trust_remote_code=True,use_flash_attention_2=True)
model =model.eval()
tokenizer = AutoTokenizer.from_pretrained('meta-llama/Meta-Llama-3-8B-Instruct',use_fast=False)
tokenizer.pad_token = tokenizer.eos_token
input_ids = tokenizer(['<s>Human: 介绍一下中国\n</s><s>Assistant: '], return_tensors="pt",add_special_tokens=False).input_ids
if torch.cuda.is_available():
  input_ids = input_ids.to('cuda')
generate_input = {
    "input_ids":input_ids,
    "max_new_tokens":512,
    "do_sample":True,
    "top_k":50,
    "top_p":0.95,
    "temperature":0.3,
    "repetition_penalty":1.3,
    "eos_token_id":tokenizer.eos_token_id,
    "bos_token_id":tokenizer.bos_token_id,
    "pad_token_id":tokenizer.pad_token_id
}
generate_ids  = model.generate(**generate_input)
text = tokenizer.decode(generate_ids[0])
print(text)"""

# torchrun --nproc_per_node 1 project_code/llama3/llama3/example_chat_completion.py --ckpt_dir project/llama3/meta-llama/Meta-Llama-3-8B-Instruct/original/ --tokenizer_path /home/gy237/project/llama3/meta-llama/Meta-Llama-3-8B-Instruct/original/tokenizer.model --max_seq_len 64 --max_batch_size 1


# # Load model directly
# from transformers import AutoTokenizer, AutoModelForCausalLM

# tokenizer = AutoTokenizer.from_pretrained("meta-llama/Meta-Llama-3.1-8B-Instruct")
# model = AutoModelForCausalLM.from_pretrained("meta-llama/Meta-Llama-3.1-8B-Instruct")

from openai import OpenAI

prompt = """
You are a medical expert tasked with evaluating the quality of the following training sample, which consists of an input (patient case or question) and/or an output (diagnosis or answer).  Determine whether the sample is of high quality for training a model to improve diagnostic reasoning ability and medical knowledge. Only respond with “Yes” or “No” based on the criteria below:
Relevance: The input is a realistic and relevant clinical scenario.
Clarity: The input is clear and well-structured.
Accuracy: The output reflects accurate medical knowledge and sound clinical judgment.
Completeness: The sample includes all necessary information for effective learning.
Input: [Insert patient case or question here]
Output: [Insert diagnosis or answer here]
High Quality: Only respond with “Yes” or “No”.
"""
prompt_ = """
Your task is to provide at least 10 accurate and distinct patient diagnoses based on the input case report.   Ensure you provide at least 10 most likely diagnoses, listed in order of likelihood, and cover a wide range of unique possibilities.  \n Follow the guidelines for a generation: 1.   Each diagnosis should be precise and unique, ensuring a variety of at least 10 possibilities.   2.   List one diagnosis per line.   3.   Generate 10 differential diagnoses related to the input case report.   Think step by step.  \n \n***Output format***:Differential diagnosis: 1.   \n2.   \n3.\n4.   \n5.   \n6.   \n7.   \n8.   \n9.   \n10.
"""


input1 = """
INPUT: how can diagnostic imaging be used in rheumatic diseases of childhood? \nOUTPUT:\ndiagnostic imaging, such as radiography or magnetic resonance imaging (mri), can be used to assess joint involvement in arthritis or to identify evidence of central nervous system involvement or myositis in certain diseases. however, it is important to note that radiographic abnormalities may lag behind the clinical examination findings." 
"""
input2 = """
INPUT: what is the function of the erector spinae muscles? \nOUTPUT:\n the erector spinae muscles extend from the sacrum to the skull and are responsible for extending the spine, maintaining posture, and facilitating movements of the head and neck.
"""
input3 = """
INPUT: What is the Clinical Description of disease SOST-Related Sclerosing Bone Dysplasias?\n OUTPUT:\nHypothesized to be allelic disorders , sclerosteosis and van Buchem disease were confirmed to be caused by pathogenic variants in the same gene in 2002 . The two disorders have very similar phenotypes caused by genetic deficiency of sclerostin; however, the manifestations of van Buchem disease are generally milder than those in sclerosteosis and syndactyly is absent (Table 2) . Taken together, these two disorders are known as SOST-related sclerosing bone dysplasias.
"""
input4 = """
INPUT: What is the Clinical Description of disease Autosomal Dominant TRPV4 Disorders?\n OUTPUT:\nThe two groups of disorders and the phenotypes comprising autosomal dominant TRPV4 disorders (listed from mildest to most severe) are:\nNeuromuscular disorders (see Table 1):\nCharcot-Marie-Tooth disease type 2C\nScapuloperoneal spinal muscular atrophy\nCongenital distal spinal muscular atrophy\nSkeletal dysplasias (see Table 2):\nFamilial digital arthropathy-brachydactyly\nAutosomal dominant brachyolmia\nSpondylometaphyseal dysplasia, Kozlowski type\nSpondyloepiphyseal dysplasia, Maroteaux type\nParastremmatic dysplasia\nMetatropic dysplasia\nThe phenotypic spectra within both neuromuscular and skeletal groups are broad and overlapping, and the phenotypes of both groups can in rare cases overlap as well .\nOf note, sensorineural hearing loss (SNHL), which is bilateral and progressive and ranges from mild to moderate, can occur in both phenotypes. Onset is from childhood to adulthood .
"""
input5 = """
INPUT: What are the possible synopsis characteristics of having disease ECTODERMAL DYSPLASIA WITH NATAL TEETH, TURNPENNY TYPEalternativeTitles?\n OUTPUT:\ninheritance: Autosomal dominant \ngrowthHeight: Short stature (5th-10th percentile) \nheadAndNeckHead: Relative macrocephaly \nheadAndNeckEyes: Thin, sparse eyebrows ;\nThin, sparse eyelashes \nheadAndNeckTeeth: Multiple natal teeth ;\nHypodontia (secondary teeth) ;\nOligodontia (secondary teeth) \nskeletalSkull: Hyperostosis of cranial vault \nskinNailsHairSkin: Flexural acanthosis nigricans (females, childhood-early adolescence) ;\nNormal sweating capacity ;\nHypoplastic pilosebaceous units ;\nHypoplastic sweat glands \nskinNailsHairNails: Normal nails (majority) \nskinNailsHairHair: Thin, slow-growing scalp hair ;\nScant axillary hair ;\nScant pubic hair ;\nFlaked, cracked, missing cuticular scales ;\nThin, sparse eyebrows ;\nThin, sparse eyelashes \nmiscellaneous: Variable heat tolerance;\nAcanthosis nigricans fades during adolescence and reappears in pregnancy;\nScalp hair quality improves during pregnancy\n
"""
input6 = """
INPUT: What are the possible synopsis characteristics of having disease ESOPHAGITIS, EOSINOPHILIC, 1; EOE1alternativeTitles?\n OUTPUT:\ninheritance: Multifactorial \ngrowthOther: Failure to thrive \nabdomenGastrointestinal: Difficulty feeding ;\nDysphagia ;\nEpigastric pain ;\nFood impaction ;\nVomiting ;\nThickening of basal epithelial layer and elongation of papillae ;\nAt least 24 eosinophils per high-power field on esophageal biopsy ;\nAbsence of eosinophilia in other intestinal segments \nmiscellaneous: Predominantly occurs in young males with high rate of atopic disease\n
"""
input7 = """
INPUT: A 43-year-old gentleman with a history of intravenous drug use presents with general fatigue and weakness accompanied by swelling in his ankles and lower legs. Further questions elicit that he has had many infections due to his drug use but has not previously had any cardiac or pulmonary issues. Upon physical examination you notice a holosystolic blowing murmur radiating to the right sternal border, which the patient denies being told about previously. Based on this presentation, what is the most likely cause of the murmur?\n\nOPTIONS: \nA: Ventricular septal defect\nB: Tricuspid stenosis\nC: Tricuspid regurgitation\nD: Mitral stenosis\nE: Mitral regurgitation\n\n OUTPUT:\nC: Tricuspid regurgitation"
"""
input8 = """
INPUT: A 65-year-old man comes to the physician because of a 2-week history of chest pain that begins after walking at a brisk pace for 2 blocks. The pain does not radiate anywhere and is hard to localize. He has had similar episodes in the past 6 months and was prescribed sublingual nitroglycerin, which helps relieve the pain. The patient has hypertension and type 2 diabetes mellitus. He takes lisinopril and metformin daily. He appears well. His temperature is 37°C (98.6°F), pulse is 75/min, and blood pressure is 145/90 mm Hg. Examination shows a regular heart rhythm. S1 and S2 are normal. The lungs are clear to auscultation. There is no peripheral edema. Which of the following is the most likely explanation for the improvement of this patient's chest pain?\n\nOPTIONS: \nA: Delayed electrical conduction\nB: Decreased venous pooling\nC: Coronary arterial vasodilation\nD: Increased atherosclerotic plaque stability\nE: Decreased end-diastolic pressure\n\"\n\n OUTPUT:\nE: Decreased end-diastolic pressure\n\
"""
input9 = """
INPUT: a 30-year-old woman presented to a local hospital with 6 months of nausea and vomiting. her symptoms progressed to early satiety, epigastric abdominal pain, and a 40-lb unintentional weight loss. computed tomography of the abdomen and pelvis revealed a 3-cm mass in the antrum with perigastric lymphadenopathy ( figure a). endoscopy conﬁrmed a 3-cm submucosal mass in the antrum. biopsies were nondiagnostic. the patient was transferred to our hospital for further workup. physical examination was signiﬁcant for an obese, soft abdomen with mild epigastric tenderness to palpation and normal active bowel sounds. laboratory evaluation was unremarkable. family history was not relevant. repeat endoscopy showed a 3-cm irregular,submucosal lesion in the antrum extending into the pylorus ( figure b). endoscopic ultrasonography (eus) showed a 3 /h110032-cm heterogeneous lesion, with hyperechoic features and irregular borders ( figure c). the lesion was in the submucosal layer and did not involve the muscularis propria. there were 2 perigastric lymph nodes, the largest measuring 8 mm. eus-guided ﬁne needleaspiration of the lesion was nondiagnostic. given the patient’s symptoms, weight loss, and the eus appearance of the lesion, asurgical consult was obtained and the patient underwent resection.\n OUTPUT:\n"Pancreatic Rest Causing Gastric Outlet Obstruction
"""
input10 = """
INPUT: a 69-year-old woman presented to the emer- gency department with symptoms suggestive of an uppergastrointestinal hemorrhage. for the preceding 4 months,she had suffered from dyspeptic-like symptoms, but had nopreceding history of peptic ulcer disease. she was on long-term aspirin for atrial ﬁbrillation with no concomitantgastroprotective therapy. physical examination revealed anunimpaired mental status, resting tachycardia of 110 bpm,and a systolic blood pressure of 100 mmhg. a full blood count revealed a normocytic anemia of 8.1 g/dl with nor-mal platelets and prothrombin time. blood biochemistryshowed an elevated urea of 22.3 mmol/l with normal cre-atinine, liver enzymes, and calcium levels. the patient was immediately resuscitated with crystal- loids and subsequently packed red cells to achieve astable hemodynamic state. high-dose oral proton-pumpinhibitor (ppi) therapy was commenced. endoscopy wasperformed 24 hours after admission ( figure a;arrows indicate view of the gastric antrum). a postliminary bar-ium meal was requested (barium meal images of gastricantrum/duodenum figures [b] supine [c]prone).\n OUTPUT:\nDouble Pylorus Gastroscopy revealed a superior gastroduodenal ﬁstula"
"""
input11 = """
INPUT: Write a brief summarizing report for this complex radiology finding. \n CONTEXT: \"The axial CT scan reveals an isolated rim enhancing lesion measuring 4.2 x 3.8 cm situated in segment VII of the liver parenchyma consistent with a hepatic abscess. Evidence of minimal perilesional edema can be appreciated.\n OUTPUT: The axial CT scan shows a lesion in segment VII of the liver measuring 4.2 x 3.8 cm, which is consistent with a hepatic abscess. The lesion is surrounded by a rim enhancement, indicating active infection. Minimal perilesional edema is also present, suggesting inflammation around the abscess. Further evaluation and treatment are necessary to manage this isolated hepatic abscess.
"""
input12 = """
INPUT: As an epidemiologist, respond to this inquiry using data and facts regarding epidemiological events. \n CONTEXT: What factors contributed to the rapid global spread of the COVID-19 pandemic?\n OUTPUT: The rapid global spread of the COVID-19 pandemic can be attributed to several factors:\n\n1. Human-to-human transmission: The primary mode of transmission for COVID-19 is through respiratory droplets when an infected person coughs, sneezes, or talks. This made it easy for the virus to rapidly spread among individuals in close proximity.\n\n2. Global travel and interconnectedness: In the modern world, people are constantly traveling internationally for various purposes. This facilitated the rapid spread of the virus across borders as infected individuals unknowingly carried the virus with them to different parts of the world.\n\n3. Asymptomatic and pre-symptomatic transmission: Many individuals infected with COVID-19 can transmit the virus even before showing any symptoms or while experiencing only mild symptoms. This made it difficult to identify and isolate infected individuals, allowing the virus to spread silently within communities.\n\n4. Lack of widespread testing and contact tracing: Limited availability of testing kits and delays in implementing effective contact tracing measures hindered efforts to identify and isolate cases early on. This led to missed opportunities for containment and allowed the virus to continue spreading.\n\n5. Population density and urbanization: Large population densities and high levels of urbanization in many areas contribute to the rapid dissemination of infectious diseases. Urban areas tend to have more crowded living conditions and increased social interactions, creating favorable conditions for viral transmission.\n\n6. Weak healthcare systems: In some regions, healthcare systems were overwhelmed by the sudden surge in COVID-19 cases, leading to a
"""
input13 = """
INPUT: A boy aged 13 years was referred for choroidal mass of the right eye. Visual acutiy was 20/60 OD and 20/20 OS. Intraocular pressures and anterior segment examination findings were normal. Fundus examination revealed orange, subretinal mass with associated subretinal fluid in the posterior pole. The lesion was followed closely and throughout a series of visits, the lesion and fluid continued to progress, the visual acuity worsened to 20/200, and the tumor mass extended closer to the fovea (Figure 1). The mass measured 15 mm in basal diameter with a thickness of 6.4 mm on B-scan ultrasonography.\n\nWhat Would You Do Next?: ['A: Photodynamic therapy', 'B: Iodine 125 plaque brachytherapy', 'C: Anti–vascular endothelial growth factor therapy injections', 'D: External beam radiotherapy']\n OUTPUT:\nCircumscribed choroidal hemangioma\n\nWhat to Do Next: B. Iodine 125 plaque brachytherapy\n\nDiscussion: \n\nCircumscribed choroidal hemangioma (CCH) is a benign, vascular tumor considered to be congenital in nature. It is classically described as an orange-red tumor, usually in the posterior pole.1 Circumscribed choroidal hemangioma is usually diagnosed when it is causing visual disturbance from exudative retinal detachment. Circumscribed choroidal hemangioma can be treated by a variety of methods including photodynamic therapy (PDT), laser photocoagulation, cryotherapy, external beam radiotherapy, stereotactic radiotherapy, proton beam radiotherapy, episcleral plaque radiotherapy, and transpupillary thermotherapy PDT.2\nThe results of PDT for CCH are very favorable; however, the exact treatment regimen of PDT for CCH varies depending on lesion size and location. In 2 studies of PDT in CCH, tumor thickness ranged from 1.9 mm to 5.9 mm (smaller than in this patient) and thicker lesions are less responsive to PDT or require more sessions.2,3 Diffuse choroidal hemangiomas and those associated with Sturge-Weber syndrome can achieve similar thicknesses, but it is unusual for true circumscribed lesions to be this thick. Additionally, placement of an intravenous catheter, infusion of verteporfin, and multiple sessions of laser with a slitlamp delivery system would be challenging for a 13-year-old patient (choice A).\nBevacizumab has been recently reported as an option for CCH treatment.4,5 Tumor thickness was not reported, but laser photocoagulation was used as adjunctive therapy for each patient. Sagong et al5 reported a case series of 3 patients receiving intravitreal bevacizumab injections as primary treatment for CCH. The tumor thickness of these patients ranged from 1.6 mm to 2.6 mm. Of note, each of these patients were also given adjunctive PDT. Bevacizumab injections were not an option in our case owing to the need for adjunctive therapy with either PDT or thermal laser, which as described above would have proved infeasible. Additionally, a tumor thickness of 6.5 mm has not been studied with bevacizumab, to our knowledge (choice C).\nSchilling et al6 published a case series of 36 eyes treated with external beam radiation for the treatment of CCH. The age of the patients ranged from 22 to 66 years. Of the tumors that received external beam radiotherapy without laser photocoagulation, none showed tumor regression on ultrasonography. In addition, Harbron et al7 published a series of 7257 children receiving external beam radiotherapy, of which 42 secondary malignant neoplasms were diagnosed. Although external beam radiotherapy may have been effective in this case, the risk of secondary malignant neoplasm outweighed benefit (choice D).\nIodine 125 plaque brachytherapy is successfully used to treat many tumors of the retina and choroid. A case study of 8 patients with CCH who underwent episcleral plaque brachytherapy was reported by López-Caballero et al.8 The tumor thickness of the patients ranged from 2.8 mm to 6.5 mm, and all tumors were successfully treated with episcleral plaque brachytherapy targeting 29 Gy to the apex. With the ability to control our surroundings with anesthesia and need for a definitive, we elected plaque brachytherapy (choice B).
"""
input14 = """
INPUT: A white woman in her early 40s presented with generalized pruritus of 10-years’ duration. She had no other medical history. The patient provided the report of a skin biopsy performed 2 years before presentation. It was described as indicating spongiotic dermatitis. She had been treated with topical corticosteroids with no control of the symptoms. Physical examination revealed erythematous papules, some of them crusted, and some excoriations located over the trunk and upper extremities (Figure 1A). In addition, some scales and fissures were seen on her lower lip (Figure 1B), sparing the surrounding skin, as well as inner mouth and upper lip. A new biopsy sample was taken to rule out actinic cheilitis.\n\nWhat Is Your Diagnosis?: ['A: Herpes simplex virus–associated pseudolymphoma', 'B: Actinic prurigo cheilitis', 'C: Cutaneous lymphoid hyperplasia', 'D: Marginal zone lymphoma']\n OUTPUT:\n Diagnosis: B. Actinic prurigo cheilitis\n\nDiscussion: \n\nMicroscopic Findings and Clinical Course: The biopsy results showed spongiosis and erosions in the epidermis and a nodular lymphocyte infiltrate in the upper and mid dermis with a peripheral mantle zone surrounding a central germinal center with cells that were CD20 positive and BCL-2 negative (Figure 2). All these findings were diagnostic of follicular cheilitis, also known as actinic prurigo (AP) cheilitis. A phototest with a solar simulator (Saalman Multitester TYP SBC LT 400) was carried out with the immediate reading negative for UV-B, UV-A, and visible light. However, erythema appeared in the area irradiated with UV-A 48 hours afterwards. Blood test results including antinuclear antibodies and complement, along with urine porphyrin analysis were normal. A diagnosis of AP with associated cheilitis was made. Treatment with narrowband UV-B at a dose of 0.1 J/cm2 was started. After 33 sessions and a cumulative dose of 4.5 J/cm2 combined with sunscreen use when outdoors, the patient was completely asymptomatic.\n\nActinic prurigo is an uncommon photosensitive disease that has generally been diagnosed in people native to Central and South America, although some series describe the disease in white patients.1,2 Its pathogenesis is not well elucidated but it has been related to human leucocyte antigen (HLA) DR4 and in particular HLA DRB1*0407, and is considered to be a type IV hypersensitivity reaction.3 Actinic prurigo usually appears in childhood, although late onset in adulthood is well described.4 The main clinical features of AP are itching and erythematous papules; vesicles and scarring can also be present. In general, the lesions appear on the face and forearms but in covered sites as well. Mucosal surfaces, such as the conjunctivae and lips, may also be affected. Some authors report a more severe course with frequent mucosal involvement in children compared with adults.5 In the acute phase, AP cheilitis biopsy results are unspecific with acanthosis, spongiosis, edema, and an inflammatory infiltrate. In a chronic phase it characteristically shows well-formed dermic lymphoid follicles as described in this patient. This pattern is considered by some authors as a very characteristic finding of AP5 and was the key to the diagnosis of this patient. Cutaneous lesions are less specific. Early lesions show epidermal spongiosis, acanthosis, and a dermal perivascular inflammatory infiltrate. Chronic lesions present lichenification, excoriations, and a heavier mononuclear infiltrate. Otherwise, the nonspecificity of symptoms and skin lesions, along with the rarity of this disease in our setting had been responsible for the diagnostic delay. Regarding other differential diagnoses for this patient, herpes simplex virus (HSV), including orolabial HSV infection, may demonstrate histologic features of pseudolymphoma without obvious viral cytopathic changes in some cases,6 but the patient's clinical presentation was not suggestive of HSV infection. Cutaneous lymphoid hyperplasia can show a similar histopathology to this case; nevertheless it has a different clinical presentation, which is typically unilesional or regionally grouped lesions.7 Marginal-zone lymphoma can also show a nodular infiltrate in the dermis, but characteristically the centers of the nodules show dark areas surrounded by a pale area, in which neoplastic Bcl-2–positive cells predominate.\nRegarding treatment, many options such as strict photoprotection, steroids, antimalarials, and thalidomide have been tried with different outcomes. Macfarlane et al1 presented UV-B desensitization as a treatment option and this is the treatment that showed the best results in this patient.\n\nConclusions: We describe an adult woman with a medical 10-year history of pruritus, who showed lesions of AP cheilitis that were biopsied and informed as follicular cheilitis giving us the diagnosis of AP, and who was treated with low doses of UVB with resolution of the pruritus.\n
"""
input15 = """
Age: 70.0\nSex: Male\nTitle: Lithium intoxication and nephrogenic diabetes insipidus: a case report and review of literature\nKeywords
: diabetes insipidus; intoxication; lithium; \nAbstract: \nLithium is one of the drugs used widely in the treatment of mood disorders. However, it has a very narrow therapeutic index and side effect
s can be seen in many organ systems, one of which affects the kidneys. We can see varying degrees of renal damage associated with acute or chronic lithium use. Lithium intoxication is diagnosed by a
 rise in the serum lithium concentration, but it must be remembered that serum levels and clinical findings do not always overlap. Treatment of lithium intoxication varies according to the clinical 
findings. There are various ways of treating lithium intoxication, but there is no specific antidote. The purpose of treatment is to remove the toxin from the body. Here we report a patient who was 
treated for lithium intoxication and developed diabetes insipidus during follow-up, and discuss the relevant literature.\nImage Caption and Description: \nImage caption: []\nImage description: []\nC
ase Report: \nA 70-year-old man was admitted to emergency service with speech difficulty and changes in his state of consciousness. He was found to be unable to walk. His general condition was poor,
 and he was agitated, confused, disorientated, and uncooperative. According to the family, he had been taking lithium for 9 years for bipolar affective disorder and had taken too much lithium on the
 previous day. There was no family history of diabetes insipidus, renal disease, or endocrine problems. On physical examination, his blood pressure was 100/60 mmHg, his heart rate was 76 beats per m
inute, and his temperature was 36.8 C. The only features of note were speech difficulty and muscle weakness.\nWhile in the emergency department, the patient's condition worsened, his agitation incre
ased, and respiratory distress developed, so he was intubated and mechanical ventilation was performed. His laboratory findings were as follows: glucose 154 mg/dL, blood urea nitrogen 16 mg/dL, crea
tinine 1.1 mg/dL, sodium 137 mmol/L, potassium 4.3 mmol/L, chloride 112 mmol/L, plasma osmolality 288 mOsm/L, and urine density 1005. His renal function tests, thyroid function tests, and adrenocort
icotropic hormone and cortisol levels were normal. His serum lithium level was 2.7 mmol/L (therapeutic range 0.6-1.2 mmol/L). The patient was admitted to the intensive care unit because of his deter
iorating clinical condition, where he received emergency hemodialysis.\nThe patient's urine output increased with 24 hours of hemodialysis (11,000 mL/24 hours). Laboratory findings at that time were
 as follows: blood urea nitrogen 14 mg/dL, creatinine 0.9 mg/dL, sodium 159 mmol/L, plasma osmolality 329 mOsm/L, and urine density 1005, so the patient was thought to have developed diabetes insipi
dus, and desmopressin was started at 6 mug three times daily via subcutaneous injection.\nBecause of the patient's worsened clinical condition, desmopressin was given immediately because there was n
ot adequate time to perform a water deprivation test or desmopressin stimulation test. On day 2 of follow-up, the patient no longer needed mechanical ventilation and was extubated. On day 4 of treat
ment with desmopressin, laboratory findings were as follows: sodium 148 mmol/L, plasma osmolality 306 mOsm/L, and urine density 1013. His urine output had returned to normal levels (2,850 mL/24 hour
s), so desmopressin was stopped. The plasma lithium level after hemodialysis was 0.5 mmol/L.\nHowever, on the following day, his serum sodium was 160 mmol/L, his plasma osmolality was 336 mOsm/L, an
d his urine output was noted to be 5,000 mL/24 hours, so treatment with desmopressin was restarted. The patient's response to desmopressin is shown in Table 1. One week later, the patient's urine ou
tput and laboratory findings had returned to normal levels (sodium 136 mmol/L, plasma osmolality 287 mOsm/L, urine density 1008), so the desmopressin was stopped. The patient recovered without seque
lae and was discharged after a psychiatry consultation.\n    OUTPUT:\n  Differential diagnosis:  \n1. Lithium intoxication  \n2. Nephrogenic diabetes insipidus  \n3. Acute kidney injury (post-lithium therapy)  \n4. Central diabetes insipidus (consider
ing potential brain involvement)  \n5. Hypernatremia secondary to diabetes insipidus  \n6. Acute respiratory distress syndrome (from agitation and confusion)  \n7. Delirium (due to lithium toxicity 
effects)  \n8. Electrolyte imbalance (sodium and potassium disturbances)  \n9. Hypovolemia (considering low blood pressure and increased urine output)  \n10. Renal concentrating defect secondary to 
chronic lithium use
"""
input16 = """
Age: 49.0\nSex: Male\nTitle: Total knee arthroplasty for Ochronosis induced knee arthropathy. Case report\nKeywords: alkaptunurea; bla
ck bone disease; homogentisic acid; ochronosis; total knee arthroplasty; \nAbstract: \nIntroduction:\nAlkaptunurea is a rare metabolic disorder with autosomal recessive genetic pattern in transmissi
on, it is characterized by accumulation of hemogenistic acid in the tissues due to deficiency of homogentisate 1,2 dioxygenase activity. Characteristically, affected patient will have dark urine and
 blackish discoloration of connective tissue, especially cartilage and bone and hence it is known as black bone disease.\nPresentation of the case:\nThe reported case is for 49 years old gentleman, 
known to have hypertension, hypothyroidism and Alkaptunurea. He presented to our facility with long standing bilateral knee pain (more in the left) with difficulty in doing daily activities. He pres
ented to our tertiary facility after failure of previous treatment measures. The patient underwent uncomplicated Robotic assisted total knee arthroplasty that resulted in significant improvement of 
his pain and function.\nConclusion:\nKnee arthroplasty is a reliable and reproducible modality in treating Ochronotic knee arthropathy and it would result in pain reduction and better function of pa
tients with such condition.\nImage Caption and Description: \nImage caption: Anteroposterior and lateral views of both knees and long film view.\nImage description: The knee was stable in anteropost
erior and varus-vulgus translation (Figure 1).\n\nImage caption: KOOS-PS score and interpretation.\nImage description: \nImage caption: Intraoperative clinical photos of the left knee.\nImage descri
ption: Gentle soft tissue handling and closure with bioabsorbable multifilament suture was done and skin closed with stables and no drain was used (Fig. 3, Fig. 4).\n\nCase Report: \nThe reported ca
se is for a 49 years old Indian gentleman, known to have hypertension, hypothyroidism and Alkaptunurea. He presented first to our tertiary center outpatient clinic in May 2018 complaining of long-st
anding bilateral knee pain which was more in the left side and chronic low back pain. He has been followed by a senior spine surgeon and the patient was managed well conservatively, regarding his kn
ees pain, different treatment modalities were tried and they never relieved the patient's symptoms. Long term physiotherapy, life style modifications were all tried with minimal effect. In 2013 and 
2016, the patient underwent arthroscopic debridement for right and left knees respectively in other facility and temporary relief was achieved. The patient is married with negative past surgical his
tory apart from what has been mentioned, not doing sport, irrelevant drug history and not smoker. He also had no family history of similar condition.\nUpon presentation, the patient had difficulty i
n ambulating for a distance due to his knees pain primarily, while his knee examination showed severe joint line tenderness and limited range of motion from 10 to 120 , his standing knees X-rays wer
e significant for severe tricompartmental osteoarthritis and correctable valgus deformity of 5 . The knee was stable in anteroposterior and varus-vulgus translation (Figure 1).\nThe patient scaled h
is knee pain as 9/10 on pain visual analogue scale and his function scored very low (28.2) on the Knee Injury and Osteoarthritis Outcome Score - physical function short form (KOOS-PS) (Figure 2).\nT
he patient was counselled for primary total knee arthroplasty as a solution for his knee disability and on July 2018, he underwent uneventful left knee arthroplasty by a senior orthopedic arthroplas
ty consultant. The surgery was day care and robotic assisted. Intraoperatively, there were significant blackish discoloration of the cartilage and surrounding tissue. However, there were no features
 of tissue necrosis or bleeding tendency and apart from the discolored tissue, the surgery was straightforward.\nIntraoperatively, the knee was stable and both cruciate ligaments were intact and hen
ce a cruciate retaining total knee cemented prosthesis was implanted successfully with patellar resurfacing via medial parapatellar approach. Gentle soft tissue handling and closure with bioabsorbab
le multifilament suture was done and skin closed with stables and no drain was used (Fig. 3, Fig. 4).\nThe patient was ambulated immediately postoperatively; however, it was noticed that he had lowe
r pain threshold and consumed maximal postoperative narcotics. the patient was discharged home safely by the end of day. At two weeks follow up, the surgical wound has healed completely with no comp
lications.\nPostoperatively, the patient started immediate outpatient accelerated physiotherapy program and at 3 months, he got improved significantly in terms of pain and functional scores. He scor
ed 4/10 on visual analogue scale and 70.3 on KOOS-PS score at 1 year. The patient was satisfied with the procedure and had a silent and painless left knee with almost no symptoms and planning to do 
the right side soon.\n    OUTPUT:\n Differential diagnosis:  \n1. Ochronosis induced knee arthropathy  \n2. Primary osteoarthritis of the knee  \n3. Secondary osteoarthritis due to prior injuries (e.g., meniscal tea
rs, ligamentous injury)  \n4. Gouty arthritis (pseudogout)  \n5. Septic arthritis  \n6. Rheumatoid arthritis  \n7. Polymyalgia rheumatica  \n8. Chondrocalcinosis  \n9. Avascular necrosis (osteonecro
sis)  \n10. Post-traumatic arthritis
"""
input17 = """
Age: 34.0\nSex: F\nTitle: Pancreaticobiliary maljunction diagnosed long after laparotomy in the neonatal period for annular pancreas: report of a case\nDescription: \nA 34-year-old woman presented to a physician with chief complaints of abdominal pain and fever. The physician suspected acute exacerbation of chronic pancreatitis and referred the patient to the Department of Gastroenterology, Fukushima Medical University Hospital. The patient had a medical history of duodenal atresia treated by emergent surgery 2 days after birth, and annular pancreas and malrotation of the intestine, for which duodenoduodenal anastomosis with Ladd’s procedure was performed. Operative findings revealed no dilatation of the common bile duct. At 9, 23, and 25 years of age, she suffered from repetitive acute pancreatitis and required hospital treatments. Since she had recurrent epigastralgia and back pain, she was diagnosed as having chronic pancreatitis and was prescribed with oral drugs. She was a non-smoker and reported occasional alcohol consumption with no relevant family history.\\nLaboratory data from blood samples taken at the patient’s first visit to our department exhibited slight elevation of hepatic and biliary tract enzymes (glutamic oxaloacetic transaminase 53 IU/L, glutamic pyruvic transaminase 94 IU/L, alkaline phosphatase 446 IU/L, gamma-glutamyl transpeptidase 259 IU/L). Abdominal computed tomography (CT) showed a small round stone, approximately 9.3 mm in diameter, in the common bile duct, and a pancreatic calculus, approximately 14 mm in diameter, in the pancreatic head duct (Fig. ), causing slight dilatation of the distal pancreatic duct. Abdominal ultrasonography showed no dilatation of the intrahepatic bile duct and no thickness of the gallbladder wall. Magnetic resonance cholangiopancreatography (MRCP) revealed annular pancreas around the second portion of the duodenum (Fig. ). Endoscopic retrograde cholangiography (ERCP) was performed to determine the cause of the pancreatitis. ERCP showed a round filling defect caused by the above-mentioned stone and pancreatic calculus (Fig. a). The distal portion of the common bile duct was bended due to the previous surgical procedures for annular pancreas in the neonatal period. Pancreaticobiliary maljunction was suspected because the contrast medium refluxed to the pancreatic duct during cholangiography (Fig. a). The common channel could not be measured exactly, because of the bended distal portion of the common bile duct. The amylase level in bile juice obtained during ERCP was elevated to 2513 U/L. The 3D-cholangiography reconstructed from the CT data (Fig. b) revealed that the pancreatic duct joined the common bile duct at the bend. Preoperative endoscopic ultrasonography was not performed in the present case. As endoscopic sphincterotomy was difficult to perform because of the deformed duodenum due to the previous surgery, only a balloon dilatation of Vater’s papilla was performed. Furthermore, removal of the common bile duct stone could not succeed. Then, we decided to perform surgical treatment. Although intraoperative cholangiography via the cystic duct showed a filling defect in the common bile duct, cholangioscopy via a small incision on the common bile duct showed no stones. Thus, we concluded that that the stone had passed spontaneously. On the basis of the preoperative findings, high levels of amylase in the gallbladder (22,300 U/L), and the presence of a relatively long common channel detected by cholangiography, our patient was diagnosed as having a pancreaticobiliary maljunction without bile duct dilatation. We performed a cholecystectomy in the laparotomy and placed a C-tube in the common bile duct. In histopathological findings, reactive lymph follicle and lymphocytic infiltration were observed around Rokitansky-Aschoff sinus in the gallbladder with no neoplastic lesion in the mucosa.\\nThe postoperative course was uneventful. The bile juice drained from the C-tube showed elevated levels of amylase (32,572 U/L). On postoperative day 13, the C-tube was removed, and the patient was discharged on postoperative day 17. At time of writing, 17 months after surgery, there has been no relapse of pancreatitis. However, medical treatment has been maintained for chronic pancreatitis in this patient.\n    OUTPUT:\n Differential diagnosis:  \n1. Chronic pancreatitis  \n2. Pancreaticobiliary maljunction  \n3. Biliary obstruction due to choledocholithiasis  \n4. Annular pancreas  \n5. Acute pancreatitis  \n6. Pancreatic duct stone disease  \n7. Duodenal atresia sequelae  \n8. Hepatobiliary infection (cholangitis)  \n9. Gallbladder disease (cholecystitis or chronic cholecystitis)  \n10. Post-surgical complications related to previous gastrointestinal surgeries
"""
input18 = """
INPUT: Age: 6.0\nSex: F\nTitle: ASSOCIATION OF MENINGITIS AND PERICARDITIS IN INVASIVE PNEUMOCOCCAL DISEASE: A RARE CASE\nDescription: \nA pr
eviously healthy 6-months-old female infant was referred to the Pediatric Intensive Care Unit of the Clinics Hospital of University of Campinas (CH-UNICAMP) because of a coma. Fifteen days prior to 
the coma, the patient had presented respiratory symptoms and had received antipyretics and short-acting B2-agonists. Four days prior to the coma, the patient presented respiratory distress and a fev
er, and was admitted to a secondary hospital in the metropolitan region of Campinas, São Paulo, Brazil. On the first day of hospitalization, the patient had a persistent fever and sinus tachycardia.
 A chest X-ray revealed an increased cardiac area with no radiographic changes in the lungs (). The following day, an echocardiography revealed pericardial thickening with bulky effusion and signs o
f cardiac tamponade. The patient was reported to be in good general condition. On the third day of hospitalization, the patient suffered from seizures. Diazepam, phenobarbital, and phenytoin were ad
ministered, and an urgent transfer to the intensive care unit was requested. During transport, the patient was intubated and was administered dobutamine. Upon arrival to the CH-UNICAMP, the patient 
went into hypotensive shock, with a Glasgow coma score of 3.\\nAfter hemodynamic stabilization, a computed tomography (CT), a lumbar puncture, radiography, blood cultures, and laboratory tests were 
performed. The initial hemogram was: Hb 6.1 g/dL; Ht 19.8%; red blood cell count 3,320,000/mm3; white blood cell count 4290/mm3 (15.3% neutrophils; 12.2% band cells; 70.4% lymphocytes; 2.1% monocyte
s); platelet count 166000/mm3. A cerebrospinal fluid (CSF) analysis revealed: Proteins 1291 mg/dL; Blood cells 730/mm3; Glucose 0 ­mg/­dL; Leukocytes 51 cells/mm3 (86% neutrophils). Numerous gram-po
tive cocci were visualized in the CSF bacterioscopy. Ceftriaxone was administered to the patient at a dose of 100 mg/kg. For hemodynamic stabilization, epinephrine was required at an infusion rate o
f 0.3 mcg/kg/ min. The CT revealed diffuse cerebral edema and chest radiography showed a discrete peribronchial heterogeneous opacity in the right hemithorax and cardiomegaly. A bedside ultrasound s
howed a septate pericardial effusion () without pulmonary consolidation. The neurological examination showed that the patient was brain dead, and a pericardiocentesis was not performed. Streptococcu
s pneumoniae was identified in the blood and CSF cultures. The bacteria were susceptible to the following antibiotics: sulfamethoxazole-trimethoprim; benzylpenicillin; erythromycin; ceftriaxone; van
comycin; and levofloxacin. Brain death was confirmed according to protocol.\n    OUTPUT:\n Differential diagnosis:  \n1. Invasive pneumococcal disease (meningitis with pericarditis)  \n2. Viral meningitis (potentially causing respiratory symptoms)  \n3. Bacterial mening
itis (other than Streptococcus pneumoniae)  \n4. Tuberculous meningitis  \n5. Encephalitis (viral or autoimmune)  \n6. Pericarditis due to viral infection (e.g., Coxsackievirus)  \n7. Congestive hea
rt failure due to non-infectious causes  \n8. Hematologic conditions (e.g., acute anemia)  \n9. Sepsis (due to severe systemic infection)  \n10. Intracranial hemorrhage (secondary to septic processe
s or sepsis-associated coagulopathy)
"""

# Your task is to provide at least 10 accurate and distinct patient diagnoses based on the input case report. Key points: 1) Diagnoses are confirmed by clinical or anatomic pathology tests, or sometimes by clinical criteria or expert opinion. 2) You will be informed at the end of the case description if diagnostic tests are being ordered to confirm the diagnosis. Ensure that you provide at least 10 most likely diagnoses, listed in order of likelihood, and cover a wide range of unique possibilities.\n Follow the guidelines for a generation: 1. Each diagnosis should be precise and unique, ensuring a variety of at least 10 possibilities. 2. List one diagnosis per line. 3. Generate at least 10 differential diagnoses related to the input case report. Think step by step.\n \n***Output format***:Differential diagnosis: 1. \n2. \n3.\n4. \n5. \n6. \n7. \n8. \n9. \n10. \n\n\n
prompt99 = """
#Background#

"""


target_part = "BBa_K3771003"
prompt100 = f"""
#Background#
1. We will provide you with a text after 'Here is the text:', which is converted from web page file, and may contain excessive and non-essential information.
2. The first line of the text is the name of a synthetic biology component, '{target_part}'.
3. The content of this web page is very irregular at present. Originally this page was supposed to describe only the function of '{target_part}', but now it contains descriptions of many other operating components related to '{target_part}', or of the entire project. It is necessary to extract the functional description and operating environment of '{target_part}' from the web page in order to better understand the characteristics and applicability of '{target_part}'.
#Task#
1. Please summarize the function of the synthetic biology component named '{target_part}' from the provided text, and provide a clear and concise description focusing on the function and usage of '{target_part}'. Your extraction should be no more than 6 paragraphs.
2. Please provide a detailed summary of the necessary operating environments for the use of '{target_part}', focusing on the strains employed. Describe the essential settings, conditions, and biological systems required for its effective use, especially any unique environmental parameters and relevant microbial or genetic strains.
3. Please ignore and remove the HTML contents that are not removed, and response with natural, fluid and accurate language.
4. Please remove meaningless and confusing symbols around words, such as '_', '\\', etc
#Role#
You are an excellent synthetic biologist, especially good at summarizing the functions of synthetic biological components, and you are always able to accurately summarize the functions of components and the required chemical and operating environment. 
#Profile#
You have the the ability to work as a researcher or analyst in the field with an in-depth understanding of synthetic biology components and their applications.
#Skills#
You are familiar with synthetic biology terminology, understanding web information extraction techniques, bioinformatics background. You can accurately distinguish between the description of '{target_part}' and the description of other components.
#Goals#
Accurately extract the functional description and operating environment of '{target_part}' from the web page. If the function or operating environment of '{target_part}' is related to other components, feel free to write other components' contents, functions, characteristics, etc.
#Constrains#
1. You should ensure that the extracted information is accurate to avoid any possible misinterpretation or information loss. 
2. If the function or operating environment of '{target_part}' is related to other components, feel free to write other components' contents, functions, characteristics, etc.
3. Please try to use the original sentences and words to summarize and keep professional terms.
#OutputFormat#
1. Please response with "FUNCTION: (functional description of '{target_part}') \nEnvironment: (operating environment of '{target_part}')"
2. Your answer should only contain the functional description and operating environment, no need for any other words.
3. If the function details are not clear, respond with 'No description of the function'.
4. If information on the operating environment or strains is insufficient, respond with 'No description of the environment'.
#Workflow#
1. Identify and locate the functional description and operating environment related to '{target_part}' in the web page.
2. Extract and organize information to ensure its accuracy and completeness.
3. If you cannot extract enough information, just output 'No description of the function' or 'No description of the environment'.
"""

input100 = """
Loading menubar.....<UNK>Experience: None<UNK>[ Get This<UNK>Part](https://parts.igem.org/partsdb/get_part.cgi?part=BBa_K3771003)<UNK>Coding<UNK># Part:BBa_K3771003<UNK>Designed by: KAO, YI-CHING   Group: iGEM21_NCKU_Tainan   (2021-09-30)<UNK>CSAD<UNK>L-Cysteine sulfinic acid decarboxylase (CSAD) is an enzyme consisting of 493<UNK>amino acids and weighs 50 kDa. CSAD functions in the taurine biosynthesis<UNK>pathway, converting L-Cysteine to taurine [1].<UNK>taurine_pathway_1.png)<UNK>Fig. 1. Taurine production pathway<UNK>CSAD is part of the L-cysteine sulfinic acid pathway, one of two possible<UNK>taurine synthesis pathways. CSAD catalyzes the decarboxylation of L-Cysteine<UNK>sulfinic acid into hypotaurine, which is spontaneously oxidized to taurine<UNK>CSAD was used in _in vivo_ testing of taurine production. The sequence for<UNK>CSAD enzyme and _trc_ promoter were ligated and transformed into _E. coli_ to<UNK>calculate taurine production using high-performance liquid chromatography<UNK>The CSAD fragment was synthesized by IDT and amplified by PCR. Agarose gel<UNK>electrophoresis result is shown in Fig. 2.<UNK>Fig. 2. Confirmation of _csad_ fragment by PCR. M: Marker; Lane 1: _csad_<UNK>Fig. 3. Confirmation of pSUI-_Ptrc-csad_ by digestion. M: Marker; Lane 1~3:<UNK>Different colonies of pSUI-_Ptrc-csad_ (3674 bp)<UNK>CSAD2-plate%28DH5a%29.png<UNK>Fig. 4. Transformation / CSAD in DH5α SDS-PAGE and western blot of CSAD enzyme<UNK>to confirm protein expression.<UNK>PAGE%28DH5a%29.png<UNK>Fig. 5. Confirmation of protein expression of CSAD. M: Marker; Lane 1: whole<UNK>cell of CSAD in DH5α; Lane 2: soluble protein of CSAD in DH5α (~50 kDa)<UNK>Taurine production yield of CSAD with other production enzymes calculated by<UNK>high-performance liquid chromatography (HPLC).<UNK>1<UNK>. Joo Y-C, Ko YJ, You SK, et al. Creating a New Pathway in Corynebacterium<UNK>glutamicum for the Production of Taurine as a Food Additive. _Journal of<UNK>Agricultural and Food Chemistry_. 2018;66(51):13454-13463.<UNK>doi:10.1021/acs.jafc.8b05093<UNK>Sequence and Features BBa_K3771008 SequenceAndFeatures<UNK>Categories<UNK>Parameters<UNK>None<UNK>gtat cgtggtagatgaggcgatcctgaagggtacgtcagcgtctgagaaggtgtgcgagtggaaggaacccgaggag<UNK>ttgaaac aattactggacctggaattgcagtcgcaaggcgaaagccgcgagcaaattttggaacgctgccgtactgt<UNK>tattcactac agtgtcaaaaccggtcacccgcgcttcttcaatcagttattctcggggttagatccccacgctctgg<UNK>caggacgcattat taccgaaagtttgaacacgtcacaatacacatacgagattgctccggtctttgttctgatggag<UNK>gaggaggttttaaaga aacttcgcgcgcttgtagggtggaatagcggcgacggtgtattctgtcctgggggatcaat<UNK>ctctaatatgtatgcgatg aaccttgcccgctttcagcgttatccagattgtaaacaacgtggactgcgcgccctgc<UNK>cccctttagctttattcacaag caaggaatgtcactacagtatcactaagggagcagcgttcttgggtctgggtact<UNK>gactccgtccgtgtcgtaaaagcgg atgagcgtgggcgtatgattccggaagatttggaacgccagatcattcttgc<UNK>cgaagccgagggttccgtgcctttcctg gtatcagctactagcgggactacggtgttgggggcatttgaccctttag<UNK>atgccatcgcagatgtatgccagcgccatgg attgtggttccacgtcgatgccgcatggggtggaagtgtcttgctg<UNK>tcccgcacacaccgccacctgctggacggaatcc agcgtgctgactctgttgcttggaatccacataagttattagc<UNK>tgcgggactgcaatgttcggctttacttcttcgcgat acgtctaacttgctgaaacgttgccacggaagccaagcgt<UNK>cttatttgtttcaacaagacaagttttacgacgtggcgct tgatacgggcgacaaggtcgtgcagtgtggacgtcgc<UNK>gtagattgcctgaaactttggttgatgtggaaagcgcagggtg gacaaggcctggagcgtcgcattgaccaagcatt<UNK>cgctctgacacgctacctggttgaagagattaaaaaacgcgaggga tttgagctggtgatggagccagagtttgtta<UNK>acgtctgcttttggttcgttcctccctccttacgtggaaaaaaagagtc gccagactatagccaacgcctttctcaa<UNK>gttgcacctgtgttaaaagaacgtatggtcaaaaagggtacgatgatgattg ggtatcagccccacggcacgcgcgc<UNK>taacttttttcgtatggttgtcgcaaacccaattcttgcccaggcagacattgat<UNK>ttcttactgggtgaattagaattattgggccaagacttgtag<UNK><UNK>"
"""

prompt101 = """
#Background#
我现在正在整理我申请PhD的个人简历(CV)，现在我在翻译我简历的过程中遇到了一些困难，请你帮助我翻译我的简历为英文。
#Task#
我会将我简历中的部分话发给你，请你将这些中文翻译为英文。
#Rules#
1. 翻译时要准确的符合现在PhD申请的事实和背景，风格要是严肃、准确的论文写作风格
2. 尽量使用专业词汇，让你的翻译看上去更加专业
3. 尽量使用论文中常用到的词汇，因为我们都经常阅读论文，都接受过良好的学术教育
#Role#
你现在将依次扮演三个角色：
1. 一位出色的中国PI，精通中文，经常进行论文写作，和阅读英文论文，擅长将一段比较通俗的话撰写为充满学术气息和专业词汇的一段话，这段话甚至能直接用到论文中
2. 一位出色的翻译家，能够将中文翻译为地道的英文，同时特别擅长翻译论文，能够精准的保留论文的精准性和专业词汇。
3. 一位出色的美国人PI，研究领域为生物学与人工智能交叉方向，你还擅长生物信息学的相关内容。现在你想招一位PhD，但是你的要求非常严格，特别在意学生简历的内容，同时你也很懂得修改简历。
#Steps#
请按照下面的步骤进行翻译，每一步都必须遵守上面的#Background#、#Task#、#Rules#、#Role#。
Step1: 现在你是出色的翻译家，精通翻译中文论文为英文论文，请将我输入的话翻译为英文，务必保留所有的信息，并尽量使用专业词汇，还要保留段落结构
Step2: 现在你是一位出色的中国PI，精通中文，经常进行论文写作和阅读英文论文，请你将翻译家翻译的话翻译为中文，要求符合你的PI身份，翻译的内容要充满学术气息和专业词汇
Step3: 现在你是一位出色的翻译家，请将中国PI翻译的内容翻译为英文
Step4: 现在你是一位出色的美国人PI，正在看学生的简历，你看到了刚才翻译家翻译的话出现在了学生的简历中，你觉得这些内容不是很专业，有些词汇不是论文中经常使用的词汇，请你给出具体的修改意见
Step5: 现在你是一位出色的中国PI，请你针对美国人PI提出修改意见修改翻译家翻译的内容
Step6: 现在你是一位出色的美国人PI，请对中国PI修改的内容进行最后的修改，直到你满意为止，注意内容信息密度要高，因为还有很多其他内容，你看到的只是其中一段话
#只需要输出以下内容#
## 美国人PI修改意见
(Step4翻译的内容)
## 美国人PI的最终修改好的内容
(Step6修改后的的内容)
##注意##
请严格按照上述的Steps进行翻译
#INPUT#
我给你的内容：
"""

input101 = """
由于代码没有公开，我重新构建了基于预训练模型进行named-entity recognition (NER) and relation extraction (RE)的 pipeline，并使用他们的数据微调模型，还使用了一系列微调techniques最终实现了更好的表现。 接下来我想要专注于Dataset entity，同时扩大数据的范围，构建跨领域的dataset-paper citation network 进行分析。
"""

prompt102 = """
#Background#
1.Here is a case report of a patient, and we want to know what disease the patient may have.
2.Diagnoses should be confirmed by clinical or anatomic pathology tests, or sometimes by clinical criteria or expert opinion.
3.You will be informed at the end of the case description if diagnostic tests are being ordered to confirm the diagnosis.
#Role#
You are an experienced attending physician, familiar with a variety of conditions, and particularly good at interpreting a patient's case report and extracting key information from it to arrive at a diagnosis.
#Task#
Follow the steps below to process the case report.
##Step1##
Now you are an excellent Resident, very good at sorting out the case report of patients and emphasizing the key points. Now, please sort out the Case report after #Case report#, which requires that the patient's information should not be added or deleted, and the key information should be highlighted to facilitate the subsequent doctors to make diagnosis.
##Step2##
You are now an excellent Radiologist, very good at analyzing imaging reports. Now, please combine the Case report after #Case report# with the data sorted out by the Resident in ##Step1## to analyze the imaging report and describe the abnormalities or pathological features found. If there is no imaging report, please skip this step and do not output.
##Step3##
You are now a multidisciplinary team (MDT) made up of outstanding specialists in various fields. You are invited to analyze the case report in terms of your area of expertise and to interpret the specialized tests (if any). Then you should give the diagnosis opinions of the case report in your own research field, and tried to help the Attending Physician to reach the ten most likely diagnoses.
##Step4##
Now you are an excellent Pathologist, very good at analyzing all kinds of pathology reports to find out the key information. Please analyze the pathological report in the Case report after #Case report# and make pathological analysis and diagnosis.
##Step5##
You are now an excellent Attending Physician, with rich experience in diagnosis, and always get the most correct diagnosis in a complex case report. Now please make a comprehensive analysis of the case report after #Case report#, the Resident's analysis, the Radiologist's analysis, the MDT's analysis, the Pathologist's analysis. Then provide at least 10 accurate and distinct patient diagnoses. Ensure that you provide at least 10 most likely diagnoses, listed in order of likelihood,  and cover a wide range of unique possibilities.
##Step6##
You are now a multi-disciplinary team (MDT) made up of outstanding specialists in various fields. Please combine the following case report after #Case report# with the professional knowledge of all your internal specialists to evaluate the diagnostic results of the Attending Physician in ##Step5##, and give the evaluation results and modification suggestions.
##Step7##
Now you are an excellent Attending Physician, with rich experience in diagnosis, and always get the most correct diagnosis in a complex case report. Now, please revise the diagnosis given by the multidisciplinary team (MDT) in ##Step6## combined with the analysis results of all other doctors and the original case report.
##Step8##
Repeat ##Step6## and ##Step7##  until the final diagnosis is given. 
Differential diagnosis: 1. \n2. \n3.\n4. \n5. \n6. \n7. \n8. \n9. \n10. 
#Constrains#
1.Each diagnosis should be precise and unique, ensuring a variety of at least 10 possibilities.
2.List one diagnosis per line.
3.Generate at least 10 differential diagnoses related to the input case report. Think step by step.
#Output format#
Please follow the format below to output. {xx} represents a placeholder. Please think and output step by step
##Step1##
{Resident's report}
##Step2##
{Radiologist's report}
##Step3##
{MDT's report}
##Step4##
{Pathologist's report}
##Step5##
{Attending Physician's diagnoses}
##Step6##
{MDT's modification suggestions}
##Step7##
{How many rounds of conversation did they have while discussing this matter?}
##Step8##
Differential diagnosis: 1. {diagnosis}\n2. {diagnosis}\n3.{diagnosis}\n4. {diagnosis}\n5. {diagnosis}\n6. {diagnosis}\n7. {diagnosis}\n8. {diagnosis}\n9. {diagnosis}\n10. {diagnosis}
#Case report#
"""
input102 = """
Dr. Suma Babu: A 67-year-old man was evaluated in the sleep clinic at this hospital because of odd behaviors during sleep, daytime sleepiness, and apnea detected on a home sleep study. Three years before the current evaluation, the patients wife noticed that the patient had vocalizations, including talking and yelling, while sleeping. He also had thrashing movements while sleeping; he fell out of bed more than once and inadvertently hit his wife during these movements. Two years before the current evaluation, the patients wife noticed that the patient had prolonged episodes of daytime sleepiness. During the episodes, he appeared to fall asleep while sitting up and was unresponsive to shaking and loud voices; several hours later, he returned to normal interaction without any intervention. The daytime sleepiness was intermittent and fluctuated in severity. Four months before the current evaluation, the patient fell asleep while washing dishes. This resulted in a fall and unstable C1 spinal fracture, which required urgent surgical repair. After the surgical repair, melatonin and trazodone were prescribed for insomnia, and abnormal movements during sleep abated. However, vocalizations during sleep  including singing, talking, and expression of fear and anger in the context of upsetting dreams  continued and were most prominent in the early morning hours. The patient also had a motor neurologic syndrome that had started before the onset of sleep symptoms, approximately 3.5 years before the current evaluation. Symptoms included progressive gait imbalance with falls, hand clumsiness, hoarse voice, and dysphagia. Serial neurologic examinations, performed over a 3-year period by multiple neuromuscular specialists, revealed slow progression of generalized fasciculations and the development of bulbar hyperreflexia, postural instability, and hypophonia, although strength in the arms and legs remained intact. Serial electromyography revealed progressive and widespread involvement of muscles showing chronic reinnervation changes, including eventual involvement of craniobulbar muscles tongue and masseter muscles. CME at NEJM.org Dr. Brian Zhao: One year before the current evaluation, magnetic resonance imaging MRI of the cervical spine revealed moderate neural foraminal narrowing at the level of C3C4 bilaterally and no central canal stenosis. Four months before the current evaluation, MRI of the head revealed a punctate subacute infarct in the left posterior centrum semiovale, chronic infarcts in the left middle frontal gyrus and right cerebellum, and nonspecific moderate-to-severe white-matter changes Fig. 1. Dr. Babu: Blood tests for paraneoplastic, nutritional, and paraproteinemic causes of the patients neurologic syndrome were unrevealing. A diagnosis of slowly progressive motor neuron disease was made, and therapy with riluzole was begun. A videofluoroscopic swallowing study revealed severe oropharyngeal dysphagia with laryngeal penetration and silent aspiration; a gastrostomy tube was placed, and tube feeding was initiated. The patient underwent a home sleep-apnea test, which showed sleep-disordered breathing with an apneahypopnea index of 20 events per hour; hypoxemia was present at rest while he was breathing ambient air. Severe oxygen de-saturation occurred with frequent respiratory events while he was asleep in the supine position. The patient was then referred to the sleep clinic for an initial evaluation. On evaluation in the sleep clinic, the patient reported that obstructive sleep apnea had been diagnosed on the basis of a home sleep study performed 1 year earlier. Multiple attempts at treatment with continuous positive airway pressure CPAP had been unsuccessful; there had been difficulty in finding a mask that fit comfortably. In addition to the sleep and motor neurologic syndrome described previously, the patients symptoms included snoring, difficulty with sleep initiation, forgetfulness, poor judgment regarding his ability to safely complete physical tasks, urinary urgency and frequency, and night sweats. He had a history of type 2 diabetes mellitus, which was well controlled with insulin and had been complicated by mild, stable, length-dependent sensory polyneuropathy; other history included hyperlipidemia, a heterozygous factor V Leiden mutation, depression, orthostatic hypotension, and gastroesophageal reflux disease. Medications included alprazolam, bupropion, fenofibrate, insulin, melatonin, metformin, riluzole, sertraline, and trazodone; there were no known drug allergies. The patient lived in New England with his wife. He was a retired engineer. He drank two alcoholic beverages per day. He did not smoke tobacco or use illicit drugs. His mother had died from an unknown cause at an elderly age; his father had died from trauma. One of his brothers had cerebrovascular disease, and another had schizophrenia. On examination, the temperature was 36.6C, the blood pressure 11260 mm Hg, the pulse 83 beats per minute, the respiratory rate 18 breaths per minute, and the oxygen saturation 96 while the patient was breathing ambient air. The body-mass index the weight in kilograms divided by the square of the height in meters was 24.2. The patient was awake, alert, and oriented, although his attention was somewhat diminished. He could recall two words out of three. Naming and repetition were intact. The pupils were equally reactive to light and accommodation. Extraocular movements were intact, and visual fields were full. Facial sensation and strength were normal. Speech was hypophonic and mildly slurred. Elevation of the palate was symmetric, and movement of the tongue was normal. Shoulder shrug was symmetric. Strength was 55 in all muscle groups. Deep-tendon reflexes were brisk in the arms, with mild spasticity in the legs. Plantar responses were normal. Vibratory sensation in the legs was mildly diminished. Results of finger-to-nose and heel-to-shin testing were normal. There were mild myoclonic movements in both hands. Alternating movements were mildly clumsy. Tone was slightly increased in the legs. The gait was on a narrow base and was unsteady; the patient was unable to walk with a tandem gait. The Rom-berg test showed truncal titubation. A sleep study to determine the appropriate positive airway pressure PAP therapy was performed. In CPAP mode, there was good control of respiratory events. Electromyographic signals revealed elevated muscle tone during rapid-eye-movement REM sleep, but there were no abnormal behaviors. Two weeks later, during a follow-up visit in the neuromuscular clinic, the patient became unresponsive to sternal rub; the vital signs and blood glucose level were normal. He was transported to the emergency department, where he returned to a normal level of consciousness without intervention. Electroencephalography EEG revealed frequent intermittent diffuse polymorphic delta slowing of the background, often with bifrontal predominance, but showed no epileptiform abnormalities. The patient was fitted with a mask for CPAP, and treatment was initiated. Several weeks after the initiation of treatment, download of CPAP data revealed good effectiveness and adherence. However, episodes of unresponsiveness increased in frequency and lasted up to 3 hours at a time. During the episodes, the patients wife was unable to arouse him despite performing a sternal rub. Modafinil was prescribed, but the episodes did not abate. The patient was admitted to the epilepsy monitoring unit for long-term monitoring and EEG. During the admission, two episodes of unresponsiveness occurred, during which the patient had a normal blood pressure, heart rate, and glucose level and EEG revealed findings consistent with sleep. A diagnostic test was performed.
"""
prompt103 = """
You are a medical expert tasked with evaluating the quality of the following training sample, which consists of an input (patient case or question) and/or an output (diagnosis or answer).
***Task***: Rate the training pair on a scale of 1 to 5 based on the criteria provided below. A higher score indicates that the training pair is of high quality and useful for enhancing models' diagnostic reasoning ability and medical knowledge.
***Rate the training pair according to the following criteria***:
1: The training pair is entirely irrelevant to improving the model's diagnostic reasoning ability and medical knowledge. The output is not aligned with the input and fails to address the input's context or question. The input and output exhibit poor writing style and formatting, making it very difficult to understand the aim of the task.
2: The input is somewhat irrelevant to improving the model's diagnostic reasoning ability and medical knowledge. The output partially addresses the input but does so inadequately, lacking depth or accuracy.
3: The input is relevant to improving the model's diagnostic reasoning ability and medical knowledge. The output is generally aligned with the input, but may lack thoroughness or clarity in its explanation or reasoning. The training pair is moderately useful but has room for improvement.
4: The input is relevant and useful for improving the model's diagnostic reasoning ability and medical knowledge. The output effectively addresses the input, demonstrating solid reasoning and appropriate depth. The training pair is of good quality, with minor issues that do not significantly detract from its usefulness.
5: The training pair is highly relevant and valuable for improving the model's diagnostic reasoning ability and medical knowledge. The output is perfectly aligned with the input, providing a comprehensive, accurate, and well-explained response. The training pair is of exceptional quality, with clear and well-structured content that is easy to follow and understand.
Input:
Output:
Response: Only respond with a score of 1, 2, 3, 4, or 5.
"""
prompt104 = """Your task is to provide at least 10 accurate and distinct patient diagnoses based on the input case report.  Key points: 1) Diagnoses are confirmed by clinical or anatomic pathology tests, or sometimes by clinical criteria or expert opinion.  2) You will be informed at the end of the case description if diagnostic tests are being ordered to confirm the diagnosis.  3) Please provide an explanation after each diagnosis, which should match the original input case report.  Ensure that you provide at least 10 most likely diagnoses, listed in order of likelihood, and cover a wide range of unique possibilities. Explanations given after each diagnosis need to be based on the input case report. \n Follow the guidelines for a generation: 1.  Each diagnosis should be precise and unique, ensuring a variety of at least 10 possibilities.  2.  List one diagnosis per line.  3.  Generate at least 10 differential diagnoses related to the input case report.  Think step by step.  \n \n***Output format***:Differential diagnosis: 1.  \n2.  \n3.\n4.  \n5.  \n6.  \n7.  \n8.  \n9.  \n10.  \n\n\n"""


def test_diagnose(prompt, input_, mo):
    client = OpenAI()
    chat_return = client.chat.completions.create(
        model=mo,
        messages=[
            {"role": "system", "content": prompt},
            {"role": "user", "content": input_},
        ],
    )
    result = chat_return.choices[0].message.content
    return result


# input_list = [input1,input2,input3,input4,input5,input6,input7,input8,input9,input10,input11,input12,input13,input14, input15, input16,input17,input18]
# for i in input_list:
#   # print(i)
#   print(test_diagnose(prompt103, i, 'gpt-4o-mini'))

# print(input_)
print("4o: ")
print(test_diagnose(prompt101, input101, "gpt-4o"))
# print('4o-mini: ')
# print(test_diagnose(prompt101, input101, 'gpt-4o-mini'))

# import json
# with open('/home/gy237/project/llama3/new_data/final_filter/MultiCaRe_PMC_Patients_PMC_CaseReport.json', 'r', encoding='utf-8') as f:
#   data = json.load(f)
# print(len(data))
# print(data[0])
