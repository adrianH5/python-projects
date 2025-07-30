import re
import os
from lxml import etree
import pubmed_parser as pp
from utils import stringify_children


# Parse the main text from PMC OA XML file
def parse_main_text(pmc_file_path):
    para_dict = pp.parse_pubmed_paragraph(pmc_file_path, all_paragraph=False)
    main_text_list = []
    for paragraph in para_dict:
        cleaned_paragraph = paragraph["text"].strip()
        main_text_list.append(cleaned_paragraph)
    main_text = "\n".join(main_text_list)
    # print(main_text)
    return main_text


def parse_sec_text(pmc_file_path):
    para_dict = pp.parse_pubmed_paragraph(pmc_file_path, all_paragraph=True)
    sec_text_list = []
    for paragraph in para_dict:
        sec = paragraph["section"]
        cleaned_paragraph = paragraph["text"].strip()
        sec_text_list.append({"section": sec, "text": cleaned_paragraph})
    return sec_text_list


# Parse the abstract from PMC OA XML file
def parse_abstract(pmc_file_path):
    info_dict = pp.parse_pubmed_xml(pmc_file_path)
    abstract = info_dict["abstract"].strip()
    # print(abstract)
    return abstract


# Parse the DAS section from PMC OA XML file
def parse_das_sec(pmc_file_path):
    pmc_tree = etree.parse(pmc_file_path)
    data_avail_sec = []
    try:
        data_avail_sec = pmc_tree.xpath(".//sec[@sec-type='data-availability']")
    except BaseException:
        pass
    try:
        data_avail_sec = pmc_tree.xpath(".//notes[@notes-type='data-availability']")
    except BaseException:
        pass
    """
    Developed based on examples from https://jats4r.org/data-availability-statements
    """
    title_node, statement_node = None, None
    if data_avail_sec is not None:
        for element in data_avail_sec:
            title_node = element.find("title")
            statement_node = element.xpath("p")
    das_title = title_node.text if title_node is not None else ""
    if statement_node is not None:
        das_statement = ""
        for node in statement_node:
            das_statement = stringify_children(node).strip()
        ext_links_nested = [node.findall("ext-link") for node in statement_node]
        refs = [node.findall("element-citation/pub-id") for node in statement_node]
        links_nested = ext_links_nested + refs
        das_links = [link.text for link_list in links_nested for link in link_list]
    else:
        das_statement = ""
        das_links = []
    das_sec = {
        "das_title": das_title,
        "das_statement": das_statement.strip(),
        "das_links": das_links,
    }
    return das_sec


def parse_all_sec(pmc_file_path):
    das_sec = parse_das_sec(pmc_file_path)
    all_sections = parse_sec_text(pmc_file_path) + [
        {"section": "DAS", "text": das_sec["das_statement"]}
    ]
    return all_sections


def search_all_sec(pmc_file_path, search_term):
    all_sections = parse_all_sec(pmc_file_path)
    filtered_sections = []
    for sec in all_sections:
        if re.search(search_term, sec["text"]):
            filtered_sections.append(sec["section"])
    filtered_sections = list(set(filtered_sections))
    return filtered_sections


def search_intro_sec(pmc_file_path, search_term):
    all_sections = parse_all_sec(pmc_file_path)
    filtered_sec_text = []
    for sec in all_sections:
        if (
            "introduction" in sec["section"].lower()
            or "background" in sec["section"].lower()
        ):
            if re.search(search_term, sec["text"]):
                filtered_sec_text.append(sec["text"])
    return filtered_sec_text


def search_links(pmc_file_path, search_term):
    das_sec = parse_das_sec(pmc_file_path)
    links = das_sec["das_links"]
    # if len(das_sec['das_links']) > 0:
    #     filtered_links = [link for link in das_sec['das_links'] if re.search(search_term, link)]
    # else:
    #     filtered_links = []
    # return filtered_links
    return links


if __name__ == "__main__":
    # Define RE patterns.
    # text_pattern = re.compile(r'(?:train|test|validation|testing|trainings?)\s*(?:set|data)|(benchmarks?)|(data\s*('
    #                           r'?:set|base)s?)|(corpus)|(corpora)|(ID)|([Aa]ccession)')
    #
    # nlp = stanza.Pipeline(lang='en', processors='tokenize')
    #
    # for xml_file in os.listdir('PMC_articles'):
    #     file_path = os.path.join('PMC_articles', xml_file)
    #     all_text = parse_main_text(file_path) + '\n' + parse_abstract(file_path) + '\n' \
    #                + parse_das_sec(file_path)['das_statement']
    #     doc = nlp(all_text)
    #     filtered_sentences = []
    #     for i, sentence in enumerate(doc.sentences):
    #         if re.search(text_pattern, sentence.text):
    #             # print(f'====== Sentence {i + 1} =======')
    #             # print(sentence.text)
    #             filtered_sentences.append(sentence.text)
    #     if len(filtered_sentences) > 0:
    #         with open(os.path.join('filtered_sentences', xml_file[:-4] + '.txt'), 'w') as f:
    #             f.write('\n'.join(filtered_sentences))
    #         print(f'Filtered sentences in {xml_file} saved to filtered_sentences folder.')
    #     else:
    #         print(f'No filtered sentences in {xml_file}.')

    # Define search term.
    search_term = "imgt.org"
    pmc_id_list = [id[:-4] for id in os.listdir("PMC_articles") if id.endswith(".xml")]
    # pmc_id_list = ['PMC8299291', 'PMC7927579', 'PMC7987156', 'PMC8295919', 'PMC10224212', 'PMC7307108', 'PMC8242547', 'PMC10222255', 'PMC8243027', 'PMC7493737', 'PMC8103774', 'PMC8443909', 'PMC7734137', 'PMC9568283', 'PMC10148713']
    section_features = {}
    for pmc_id in pmc_id_list:
        file_name = pmc_id + ".xml"
        file_path = os.path.join("PMC_articles", file_name)
        citation_location = search_all_sec(file_path, search_term)
        if len(citation_location) > 0:
            section_features[pmc_id] = citation_location
        intro_text = search_intro_sec(file_path, search_term)
        # if len(intro_text) > 0:
        #     section_features[pmc_id] = intro_text
        # links = search_links(file_path, search_term)
        # if len(links) > 0:
        #     section_features[pmc_id] = links

    for key, value in section_features.items():
        print(f"{key}: {value}")
