import os
from lxml import etree
from utils import read_xml, stringify_children
from pubmed_oa_parser import parse_pubmed_xml


class PMCDataElement:
    def __init__(self, pmid, pmcid, title, abstract, das, refs, in_text_urls):
        self.pmid = pmid
        self.pmcid = pmcid
        self.title = title
        self.abstract = abstract
        self.das = das
        self.refs = refs
        self.in_text_urls = in_text_urls


def parse_das_sec(pmc_file_path):
    pmc_tree = etree.parse(pmc_file_path)
    # article_meta = pmc_tree.find(".//article-meta")
    # if article_meta is not None:
    #     pmid_node = article_meta.find("article-id[@pub-id-type='pmid']")
    #     pmc_node = article_meta.find('article-id[@pub-id-type="pmc"]')
    # else:
    #     pmid_node = None
    #     pmc_node = None
    # pmid = pmid_node.text if pmid_node is not None else ""
    # pmcid = pmc_node.text if pmc_node is not None else ""
    # pub_month_node = pmc_tree.find(".//pub-date/month")
    # pub_month = pub_month_node.text if pub_month_node is not None else "01"
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
        # das_statement = " ".join([node.text for node in statement_node if node.text is not None])
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
    # return pmid, pmcid, pub_month, title, statement, links
    das_sec = {
        "das_title": das_title,
        "das_statement": das_statement,
        "das_links": das_links,
    }
    return das_sec


def parse_pubmed_references(path):
    tree = read_xml(path)
    # dict_article_meta = parse_article_meta(tree)
    # pmid = dict_article_meta["pmid"]
    # pmc = dict_article_meta["pmc"]
    references = tree.xpath(".//ref-list/ref[@id]")
    dict_refs = list()
    for reference in references:
        ref_id = reference.attrib["id"]

        if reference.find("mixed-citation") is not None:
            ref = reference.find("mixed-citation")
        elif reference.find("element-citation") is not None:
            ref = reference.find("element-citation")
        else:
            ref = None

        if ref is not None:
            if "publication-type" in ref.attrib.keys() and ref is not None:
                if ref.attrib.values() is not None:
                    journal_type = ref.attrib.values()[0]
                else:
                    journal_type = ""
                names = list()
                if ref.find("name") is not None:
                    for n in ref.findall("name"):
                        name = " ".join([t.text or "" for t in n.getchildren()][::-1])
                        names.append(name)
                elif ref.find("person-group") is not None:
                    for n in ref.find("person-group"):
                        name = " ".join(
                            n.xpath("given-names/text()") + n.xpath("surname/text()")
                        )
                        names.append(name)
                if ref.find("article-title") is not None:
                    article_title = stringify_children(ref.find("article-title")) or ""
                    article_title = article_title.replace("\n", " ").strip()
                else:

                    article_title = ""
                if ref.find("source") is not None:
                    journal = ref.find("source").text or ""
                else:
                    journal = ""
                if ref.find("year") is not None:
                    year = ref.find("year").text or ""
                else:
                    year = ""
                if len(ref.findall("pub-id")) >= 1:
                    for pubid in ref.findall("pub-id"):
                        if "doi" in pubid.attrib.values():
                            doi_cited = pubid.text
                        else:
                            doi_cited = ""
                        if "pmid" in pubid.attrib.values():
                            pmid_cited = pubid.text
                        else:
                            pmid_cited = ""
                else:
                    doi_cited = ""
                    pmid_cited = ""
                if ref.find("uri") is not None:
                    url = ref.find("uri").text
                else:
                    url = ""
                dict_ref = {
                    # "pmid": pmid,
                    # "pmc": pmc,
                    "ref_id": ref_id,
                    "pmid_cited": pmid_cited,
                    "doi_cited": doi_cited,
                    "article_title": article_title,
                    "name": "; ".join(names),
                    "year": year,
                    "journal": journal,
                    "journal_type": journal_type,
                    "url": url,
                }
                dict_refs.append(dict_ref)
    if len(dict_refs) == 0:
        dict_refs = None
    return dict_refs


def parse_in_text_url(path):
    in_text_urls = []
    tree = read_xml(path)

    paragraphs = tree.xpath("//body//p")
    dict_pars = list()
    for paragraph in paragraphs:
        for ext_link in paragraph.getchildren():
            if "ext-link-type" in ext_link.attrib.keys():
                # url_link = ext_link.attrib["xlink:href"]
                in_text_urls.append(ext_link.text)
    return in_text_urls


if __name__ == "__main__":
    pmc_fulltext_path = "/data/xzuo/Projects/dissertation/dataset_URL_parser/paper_oriented/litcovid_pmc_fulltext/xml"
    current_filelist = os.listdir(pmc_fulltext_path)
    for i, pmc_file in enumerate(current_filelist):
        pmc_file_path = os.path.join(pmc_fulltext_path, pmc_file)
        pmc_meta = parse_pubmed_xml(pmc_file_path)
        refs = parse_pubmed_references(pmc_file_path)
        das_sec = parse_das_sec(pmc_file_path)
        in_text_urls = parse_in_text_url(pmc_file_path)
        pmc = PMCDataElement(
            pmc_meta["pmid"],
            pmc_meta["pmc"],
            pmc_meta["full_title"],
            pmc_meta["abstract"],
            das_sec,
            refs,
            in_text_urls,
        )
        print(pmc.pmid, pmc.das, pmc.refs, pmc.in_text_urls)
        if i == 1:
            break
