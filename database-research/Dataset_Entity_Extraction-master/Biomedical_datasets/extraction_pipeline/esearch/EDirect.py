# export PATH=/home/gy237/anaconda3/bin:/home/gy237/.local/bin:/home/gy237/bin:/opt/slurm/current/bin:/usr/local/bin:/usr/bin:/usr/local/sbin:/usr/sbin:/opt/dell/srvadmin/binexport PATH=/home/gy237/edirect:${PATH}

import requests
import subprocess
import time
import os

API_KEY = "c7929124dff6b45f8ea5b2ccf8301a286508"
# export PATH=${HOME}/edirect:${PATH}

os.environ["NCBI_API_KEY"] = API_KEY


# 执行 EDirect 的 esearch，并通过 efetch 分批获取 PMIDs
def get_pmids(query, total_records):
    """通过 EDirect 分批获取 PubMed 中符合条件的 PMIDs"""
    pmid_list = []
    batch_size = 10000  # EDirect 每次最多返回 9999 条记录
    fetched_records = 170000

    while fetched_records < total_records:
        esearch_command = [
            "esearch",
            "-db",
            "pubmed",
            "-query",
            query,
            "|",
            "efetch",
            "-format",
            "uid",  # , "-start", str(fetched_records + 1), "-stop", str(fetched_records + batch_size)
        ]
        # time.sleep(3)
        # print(" ".join(esearch_command))

        # 执行命令
        result = subprocess.run(
            " ".join(esearch_command), shell=True, capture_output=True, text=True
        )
        pmid_batch = result.stdout.strip().split("\n")
        pmid_list.extend(pmid_batch)
        fetched_records += len(pmid_batch)
        print(f"已获取 {len(pmid_batch)} 条记录，总共已获取 {fetched_records} 条记录")

        # 提前终止循环，如果没有更多记录
        if len(pmid_batch) == 1:
            print("No more records to fetch. Exiting...")
            print(pmid_batch)
            print(result)
            exit()

    return pmid_list


# 使用 EDirect 的 elink 批量将 PMIDs 转换为 PMCIDs
def get_pmcids(pmid_list):
    """通过 elink 批量将 PMIDs 转换为 PMCIDs"""
    pmcid_list = []
    batch_size = 100  # 每次转换的PMID数量

    for i in range(0, len(pmid_list), batch_size):
        pmid_batch = pmid_list[i : i + batch_size]

        elink_command = [
            "elink",
            "-db",
            "pubmed",
            "-db",
            "pmc",
            "-target",
            "pmc",
            "-id",
            ",".join(pmid_batch),
            "|",
            "efetch",
            "-format",
            "uid",
        ]

        result = subprocess.run(
            " ".join(elink_command), shell=True, capture_output=True, text=True
        )
        pmcid_batch = result.stdout.strip().split("\n")
        pmcid_list.extend(pmcid_batch)
        print(
            f"已获取 {len(pmcid_batch)} 个 PMCID，总共已获取 {len(pmcid_list)} 个 PMCID"
        )

    return pmcid_list


def fetch_pmcids(pmids):
    """使用 elink 从 PMIDs 中获取 PMCIDs"""
    url = "https://eutils.ncbi.nlm.nih.gov/entrez/eutils/elink.fcgi"
    pmcids = []
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

        # 解析 JSON，获取 PMCID
        if "linksets" in data:
            # pmcids.extend(data['linksets'][0]['linksetdbs'][0]['linksets']['links'])
            for linkset in data["linksets"]:
                if "linksetdbs" in linkset:
                    for linksetdb in linkset["linksetdbs"]:
                        if (
                            linksetdb["dbto"] == "pmc"
                            and linksetdb["linkname"] == "pubmed_pmc"
                            and "links" in linksetdb
                        ):
                            pmcids.extend(linksetdb["links"])
        print(len(pmcids))

    pmcid_list = [f"PMC{i}" for i in pmcids]
    return pmcid_list


# 查询的关键词
query = '''"ClinicalTrials.gov" or "clinical trials"'''
repo_name = "clinical_trials"

# 总共的记录数量
url = "https://eutils.ncbi.nlm.nih.gov/entrez/eutils/esearch.fcgi"
params = {"db": "pubmed", "term": query, "retmode": "json"}
response = requests.get(url, params=params)
data = response.json()
total_records = int(data["esearchresult"]["count"])  # 根据你返回的数据
print(f"total_records: {total_records}")
total_records += 1000


# 通过 EDirect 获取超过 9999 条的 PMID 列表
pmid_list = get_pmids(query, total_records)  # total_records
with open(
    f"/home/gy237/project/Biomedical_datasets/extraction_pipeline/esearch/{repo_name}_pmid.txt",
    "w",
) as f:
    for item in pmid_list:
        f.write(f"{item}\n")


# 根据 PMID 列表获取对应的 PMCIDs
# pmcid_list = get_pmcids(pmid_list)
pmcid_list = fetch_pmcids(pmid_list)
with open(
    f"/home/gy237/project/Biomedical_datasets/extraction_pipeline/esearch/{repo_name}_pmcid.txt",
    "w",
) as f:
    for item in pmcid_list:
        f.write(f"{item}\n")
print(len(pmid_list))
print(len(pmcid_list))


# {'header': {'type': 'elink', 'version': '0.3'}, 'linksets': [{'dbfrom': 'pubmed', 'ids': ['12345678', '27681005', '35771962'], 'linksetdbs': [{'dbto': 'pmc', 'linkname': 'pubmed_pmc', 'links': ['9516129', '5373931']}, {'dbto': 'pmc', 'linkname': 'pubmed_pmc_refs', 'links': ['11369533', '11355645', '11302076', '11291324', '11162367', '11150054', '11149940', '11045408', '11043374', '10953016', '10929160', '10655971', '10642416', '10641351', '10561639', '10391885', '10219036', '9945387', '9811334', '10905344', '10569350', '10545809', '10467520', '10354713', '10216622', '9989773', '9558038', '9527390', '8777327', '8464486', '8218987', '7680285', '7360347', '6877460', '6853210', '6791774', '6707905', '11029388', '5193259', '4841452', '4047805']}, {'dbto': 'pmc', 'linkname': 'pubmed_pmc_local', 'links': ['9516129', '5373931']}]}]}
# 最终获取的 PMCID 列表: {'12345678': '5373931'}
