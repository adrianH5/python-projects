import re


def match_url(url_patterns, url):
    url


def match_name(name_patterns, text):
    if name_patterns.search(text):
        first_match = name_patterns.search(text).group(0)
        return first_match
    else:
        return None


if __name__ == "__main__":
    url_patterns = re.compile(r"(covid.cdc.gov)")
    name_patterns = re.compile(
        r"(N3C)|(National COVID Cohort Collaborative)|(GenBank)|\
                     (GISAID)|(Nextstrain)|(OpenICPSR)|(CORD-19)|(LitCovid)|(NCBI Virus)"
    )
