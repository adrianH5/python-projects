from langchain_openai import ChatOpenAI
from langchain.schema import HumanMessage, SystemMessage


class SummarizerAgent:
    def __init__(self, llm_api_key, temperature=0.3, model_to_use="gpt-4o"):
        self.llm = ChatOpenAI(
            model=model_to_use, api_key=llm_api_key, temperature=temperature
        )

    def run(self, excerpt_text, book_title, chunk_index):
        """
        Summarize the excerpt, quoting passages that highlight social isolation.
        Incorporate inline citations: e.g. (book_title, chunk_index).
        """
        system_prompt = SystemMessage(
            content=(
                "You are a helpful literary assistant specialized in summarizing text. "
                "Please produce a detailed, multi-paragraph summary focusing on signs of isolation. "
                "When you quote or paraphrase something from the excerpt, add an inline citation "
                f'like this: "…"( {book_title}, chunk {chunk_index} ) at the end of the sentence. Try to use multiple citations throughout the book'
                "Be thorough and include direct quotes if relevant."
            )
        )
        user_prompt = HumanMessage(
            content=f"Excerpt:\n{excerpt_text}\n\nSummarize with citations."
        )
        response = self.llm([system_prompt, user_prompt])
        return response.content


class ThematicAgent:
    def __init__(self, llm_api_key, temperature=0.3, model_to_use="gpt-4o"):
        self.llm = ChatOpenAI(
            model=model_to_use, api_key=llm_api_key, temperature=temperature
        )

    def run(self, summary, book_title):
        """
        Focus on analyzing the theme of social isolation.
        Reference any citations from the summary and keep them intact.
        """
        system_prompt = SystemMessage(
            content=(
                "You are an analyst focusing on the theme of social isolation. "
                "Please produce a thorough, multi-paragraph analysis. "
                "Preserve any inline citations from the summary."
            )
        )
        user_prompt = HumanMessage(
            content=(
                f"Here is a summary with citations:\n\n{summary}\n\n"
                f"Analyze how {book_title} portrays social isolation. "
                "Incorporate (and preserve) existing citations wherever relevant."
            )
        )
        response = self.llm([system_prompt, user_prompt])
        return response.content


class CriticAgent:
    def __init__(self, llm_api_key, temperature=0.3, model_to_use="gpt-4o"):
        self.llm = ChatOpenAI(
            model=model_to_use, api_key=llm_api_key, temperature=temperature
        )

    def run(self, analysis):
        """
        Critique for clarity, coherence, completeness.
        Suggest expansions or deeper insight if the text is too short or missing detail.
        """
        system_prompt = SystemMessage(
            content="You are a critical reviewer tasked with improving the text."
        )
        user_prompt = HumanMessage(
            content=(
                "Critique the following analysis for clarity, coherence, completeness, "
                "and depth of discussion on social isolation. "
                "Suggest any specific improvements or expansions.\n\n"
                f"{analysis}"
            )
        )
        response = self.llm([system_prompt, user_prompt])
        return response.content


class ModeratorAgent:
    def __init__(self, llm_api_key, temperature=0.3, model_to_use="gpt-4o"):
        self.llm = ChatOpenAI(
            model=model_to_use, api_key=llm_api_key, temperature=temperature
        )

    def run(self, original, critique):
        """
        Incorporate the critique suggestions to produce a final, refined analysis,
        preserving or expanding citations. Encourage a longer output if needed.
        """
        system_prompt = SystemMessage(
            content=(
                "You are a moderator who merges suggestions into the final text. "
                "Produce a revised version with improved clarity, detail, and structure. "
                "Preserve inline citations. Expand if the critique suggests more depth."
            )
        )
        user_prompt = HumanMessage(
            content=(
                f"Original analysis:\n{original}\n\n"
                f"Critique:\n{critique}\n\n"
                "Please merge critique suggestions, retain citations, and produce a final, "
                "detailed analysis."
            )
        )
        response = self.llm([system_prompt, user_prompt])
        return response.content


def multi_agent_collaboration(
    excerpt_text,
    book_title,
    chunk_index,
    api_key,
    temperature=0.3,
    model_to_use="gpt-4o",
):
    """
    Example of the multi-agent pipeline on a single excerpt or summary chunk.
    """
    summarizer = SummarizerAgent(api_key, temperature, model_to_use)
    thematic = ThematicAgent(api_key, temperature, model_to_use)
    critic = CriticAgent(api_key, temperature, model_to_use)
    moderator = ModeratorAgent(api_key, temperature, model_to_use)

    # Summarize excerpt (with inline citations)
    summary = summarizer.run(excerpt_text, book_title, chunk_index)
    # Thematic analysis
    analysis = thematic.run(summary, book_title)
    # Critique
    critique = critic.run(analysis)
    # Merge
    final = moderator.run(analysis, critique)
    return final
