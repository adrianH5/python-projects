import requests
import time

API_KEY = "c7929124dff6b45f8ea5b2ccf8301a286508"


def fetch_all_pmids(query, total_count):
    url = "https://eutils.ncbi.nlm.nih.gov/entrez/eutils/esearch.fcgi"
    pmids = []
    batch_size = 100  # 每次获取100条
    for start in range(0, total_count, batch_size):
        params = {
            "db": "pubmed",
            "term": query,
            "retstart": start,
            "retmax": batch_size,
            "retmode": "json",
            "api_key": API_KEY,
        }
        # time.sleep(3)
        response = requests.get(url, params=params)
        # print(response.text)
        data = response.json()
        pmids.extend(data["esearchresult"]["idlist"])
        print(f"已获取 {len(pmids)} / {total_count} 个PMID")

    return pmids


def fetch_pmcids(pmids):
    """使用 elink 从 PMIDs 中获取 PMCIDs"""
    url = "https://eutils.ncbi.nlm.nih.gov/entrez/eutils/elink.fcgi"
    pmcid_dict = {}
    for i in range(0, len(pmids), 100):  # 批量处理，每次处理最多100个PMID
        pmid_batch = pmids[i : i + 100]
        params = {
            "dbfrom": "pubmed",
            "db": "pmc",
            "id": ",".join(pmid_batch),
            "retmode": "json",
            "api_key": API_KEY,
        }
        time.sleep(3)
        response = requests.get(url, params=params)
        data = response.json()
        print(data)
        exit()

        # 解析 JSON，获取 PMCID
        if "linksets" in data:
            for linkset in data["linksets"]:
                if "linksetdbs" in linkset:
                    for linksetdb in linkset["linksetdbs"]:
                        if linksetdb["dbto"] == "pmc" and "links" in linksetdb:
                            for pmcid in linksetdb["links"]:
                                pmid = linkset["ids"][0]
                                pmcid_dict[pmid] = pmcid
    return pmcid_dict


query = '''"ClinicalTrials.gov" or "clinical trials"'''

url = "https://eutils.ncbi.nlm.nih.gov/entrez/eutils/esearch.fcgi"
params = {"db": "pubmed", "term": query, "retmode": "json"}
response = requests.get(url, params=params)
data = response.json()
total_count = int(data["esearchresult"]["count"])  # 根据你返回的数据

pmids = fetch_all_pmids(query, total_count)

with open(
    f"/home/gy237/project/Biomedical_datasets/extraction_pipeline/esearch/{query}.json",
    "w",
    encoding="utf-8",
) as file:
    json.dump(pmids, file, ensure_ascii=False, indent=4)

# 打印前10个PMID作为示例
print(len(pmids))
print(pmids[:10])


pmcid_mapping = fetch_pmcids(pmids)

# 示例：打印前 10 个 PMID 和 PMCID 对应关系
for pmid, pmcid in list(pmcid_mapping.items())[:10]:
    print(f"PMID: {pmid} -> PMCID: {pmcid}")
