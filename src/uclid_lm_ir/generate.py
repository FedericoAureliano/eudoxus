import ast
import inspect
import os

from .module import Module
from .printer import print_uclid5
from .utils import Kind, log


def get_api_description() -> str:
    source = inspect.getsource(Module)
    index = source.find("def __str__")
    source = source[:index]
    # remove trailing new lines
    source = source.rstrip()
    return source


def get_prompt(task) -> str:
    """Returns the prompt for the GPT-4 API."""
    if task.endswith("."):
        task = task[:-1]

    prompt = "Extend the `Module` class below to complete the following task:"
    prompt += " " + task + ". Reply with your code inside one unique code block."
    module_class = "```python3\n" + get_api_description() + "\n```\n"
    prompt += f"\n\n{module_class}\n```python3\n#TODO\n"
    log(prompt, Kind.GENERATOR, "generated prompt")
    return prompt


def extract_code(output) -> str:
    """Extracts the code from the GPT-4 API response."""
    # replace any occurrences of "``````" with "```"
    output = output.replace("``````", "```")

    end_index = output.rfind("```")
    before_start = output.rfind("```", 0, end_index)
    # find the newline after the index
    start_index = output.find("\n", before_start + 1)

    # extract the code
    code = output[start_index:end_index]
    # remove trailing new lines
    code = code.rstrip()

    log(code, Kind.GENERATOR, "extracted code")
    return code


def process_code(code) -> str:
    parsed = ast.parse(code)
    # extract all the classes and nothing else
    parsed.body = [node for node in parsed.body if isinstance(node, ast.ClassDef)]
    output = print_uclid5(parsed)
    # remove empty lines
    output = "\n".join([line for line in output.split("\n") if line.strip()])
    log(output, Kind.GENERATOR, "processed UCLID5 code")
    return output


def gpt4_write_code(task, engine="gpt-4-0613"):
    """Generates code for a given task using the GPT-4 API."""

    log(task, Kind.USER, "task")

    import openai

    openai.api_key = os.environ["OPENAI_API_KEY"]

    prompt = get_prompt(task)

    response = openai.ChatCompletion.create(
        model=engine, messages=[{"role": "user", "content": prompt}]
    )
    response = response["choices"][0]["message"]["content"]
    log(response, Kind.LLM, "response from GPT-4")

    code = extract_code(response)
    code = process_code(code)

    def remove_question_marks(code) -> str:
        """Ask the llm to remove the question marks."""
        if "??" not in code:
            return code

        prompt = "Fix the UCLID5 code below by replacing every occurrence of `??` "
        prompt += f"with the correct value:\n```uclid5\n{code}\n```\n"
        log(prompt, Kind.GENERATOR, "prompt to remove question marks")
        response = openai.ChatCompletion.create(
            model=engine, messages=[{"role": "user", "content": prompt}]
        )
        response = response["choices"][0]["message"]["content"]
        log(response, Kind.LLM, "response from GPT-4")
        code = extract_code(response)
        return code

    code = remove_question_marks(code)
    return code
