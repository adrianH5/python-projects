from bs4 import BeautifulSoup
import re
import os
import json
from tqdm.std import tqdm
import tarfile


def parse_xml_with_beautifulsoup(xml_content):
    # Load the XML file
    # with open(file_path, 'r', encoding='utf-8') as file:
    #     xml_content = file.read()

    # Parse the XML file
    soup = BeautifulSoup(xml_content, "xml")

    # Initialize a dictionary to hold the extracted data
    extracted_data = {
        "journal-title": None,
        "pmid": None,
        "pmc": None,
        "doi": None,
        "article-title": None,
        "abstract": None,
        "introduction": None,
        "citation2rid": {},
        "references": [],
    }
    citation_list = []

    # Extracting various information
    extracted_data["journal-title"] = (
        soup.find("journal-title").text if soup.find("journal-title") else None
    )
    extracted_data["pmid"] = (
        soup.find("article-id", {"pub-id-type": "pmid"}).text
        if soup.find("article-id", {"pub-id-type": "pmid"})
        else None
    )
    extracted_data["pmc"] = (
        soup.find("article-id", {"pub-id-type": "pmc"}).text
        if soup.find("article-id", {"pub-id-type": "pmc"})
        else None
    )
    extracted_data["doi"] = (
        soup.find("article-id", {"pub-id-type": "doi"}).text
        if soup.find("article-id", {"pub-id-type": "doi"})
        else None
    )
    extracted_data["article-title"] = (
        soup.find("article-title").text if soup.find("article-title") else None
    )
    extracted_data["abstract"] = (
        soup.find("abstract").text if soup.find("abstract") else None
    )

    # Extracting introduction (this might require custom logic)
    body = soup.find("body")
    if body:
        sections = body.find_all("sec")
        for section in sections:
            # section = replace_with_rid(section)
            if "introduction" in section.find("title").text.lower():
                for citation in section.find_all("xref", {"ref-type": "bibr"}):
                    citation_list.append(citation["rid"])
                extracted_data["introduction"] = " ".join(
                    p.prettify() for p in section.find_all("p")
                )
            elif "background" in section.find("title").text.lower():
                for citation in section.find_all("xref", {"ref-type": "bibr"}):
                    citation_list.append(citation["rid"])
                extracted_data["introduction"] = " ".join(
                    p.prettify() for p in section.find_all("p")
                )
            elif "review" in section.find("title").text.lower():
                for citation in section.find_all("xref", {"ref-type": "bibr"}):
                    citation_list.append(citation["rid"])
                extracted_data["introduction"] = " ".join(
                    p.prettify() for p in section.find_all("p")
                )

                # for p in section.find_all('p'):
                #     text = replace_number_with_rid(p.text,extracted_data['citation_list'])
                #     print(text)

    # Buliding a dict for mapping citation number to rid
    citation_list = list(set(citation_list))
    for rid in citation_list:
        match = re.search(r"\d+$", rid)
        if match:
            number = int(match.group())
            extracted_data["citation2rid"][number] = rid

    # Extracting references
    refs = soup.find_all("ref")
    for ref in refs:
        rid = ref.attrs.get("id")
        pmid = (
            ref.find("pub-id", attrs={"pub-id-type": "pmid"}).text
            if ref.find("pub-id", attrs={"pub-id-type": "pmid"})
            else None
        )
        title = ref.find("article-title").text if ref.find("article-title") else None
        authors = [
            " ".join(
                [name.text for name in author.find_all(["surname", "given-names"])]
            )
            for author in ref.find_all("name")
        ]
        extracted_data["references"].append(
            {"rid": rid, "pmid": pmid, "title": title, "authors": authors}
        )

    return extracted_data


import xml.etree.ElementTree as ET
from xml.dom import minidom


def pretty_print_xml(xml_file):
    # 解析XML文件
    tree = ET.parse(xml_file)
    root = tree.getroot()

    # 将ElementTree转换为字符串
    xml_str = ET.tostring(root, encoding="utf-8")

    # 使用minidom进行格式化，使得XML结构清晰可读
    pretty_xml = minidom.parseString(xml_str).toprettyxml(indent="    ")

    output_file = "/home/gy237/project/Biomedical_datasets/extraction_pipeline/pumbed_full_text/test.xml"
    # 保存格式化后的XML
    with open(output_file, "w", encoding="utf-8") as f:
        f.write(pretty_xml)


file_path = "/gpfs/gibbs/project/xu_hua/shared/process_xml/xml"
all_tar_files = os.listdir(file_path)
all_tar_files = [i for i in all_tar_files if i.endswith(".tar.gz")]
print(len(all_tar_files))

all_faild = []
for i, name in enumerate(all_tar_files):
    filter_list = []
    faild_list = []
    with tarfile.open(f"{file_path}/{name}", "r:gz") as tar:
        print("-" * 100)
        print(name)
        for member in tqdm(tar.getmembers()):
            pmcid = member.name.split("/")[-1].split(".")[0]
            print(pmcid)
            if member.name.endswith(".xml"):
                f = tar.extractfile(member)
                if f is not None:
                    pretty_print_xml(f)
                    # xml_content = f.read()
                    print(xml_content)
                    exit()
                    try:
                        data = parse_xml_with_beautifulsoup(xml_content)
                        filter_list.append(data)
                    except:
                        faild_list.append(f"{tar_file}//{member.name}")
                        data = parse_xml_with_beautifulsoup(xml_content)
                        result_list.append(data)

    all_faild.append(faild_list)
    with open(f"xml_{i}.json", "w") as f:
        json.dump(filter_list, f, indent=4)
