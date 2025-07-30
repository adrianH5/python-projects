from langchain_openai import ChatOpenAI
from langchain.schema import SystemMessage, HumanMessage


def generate_comparative_report(
    book_summaries, api_key, temperature=0.3, model_to_use="gpt-4.5-preview"
):
    """
    Given a dict {book_title: summary_text}, produce a multi-paragraph comparative essay.
    Instruct the model to preserve or incorporate citations from each summary.
    """
    llm = ChatOpenAI(model=model_to_use, api_key=api_key, temperature=temperature)
    system_prompt = SystemMessage(
        content=(
            "You are a literary analysis assistant. "
            "Write a FIVE PARAGRAPH comparative essay on how each book treats the theme of social isolation. "
            "Paragraph 1: Introduction & thesis. "
            "Paragraph 2,3,4: Each book individually, plus deeper comparative points, with direct references and citations if available. "
            "Paragraph 5: Conclusion summarizing the comparisons. "
            "Preserve any inline citations from the provided summaries. "
            "Please be thorough and detailed in your analysis. Ensure that there are 5 paragraphs only."
        )
    )

    # Combine the per-book summaries
    user_content = "Here are summaries of the 3 books (with citations):\n"
    for book, summary in book_summaries.items():
        user_content += f"\n=== {book} ===\n{summary}\n"
    user_content += "\nNow produce the final comparative essay with proper citations."

    user_prompt = HumanMessage(content=user_content)

    response = llm([system_prompt, user_prompt])
    return response.content


def self_refine_report(draft_report, api_key):
    llm = ChatOpenAI(model="gpt-4.5-preview", api_key=api_key, temperature=0.2)
    system_prompt = SystemMessage(
        content="You are a refinement engine. Improve clarity, fix any inaccuracies, ensure correct citations."
    )
    user_prompt = HumanMessage(content=f"Refine this report:\n\n{draft_report}")
    response = llm([system_prompt, user_prompt])
    return response.content
