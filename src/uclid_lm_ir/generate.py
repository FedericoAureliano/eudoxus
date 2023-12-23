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
    preamble = "Extend the `Module` class below to complete the following tasks:"
    module_class = "```python3\n" + get_api_description() + "\n```\n"
    prompt = f"{preamble} {task}\n\n{module_class}\n```python3\n#Your code goes here!\n"
    log(prompt, Kind.GENERATOR, "generated prompt")
    return prompt


def extract_code(output) -> str:
    """Extracts the code from the GPT-4 API response."""
    # find the last instance of ```python3
    index = output.rfind("```python3")

    if index == -1:
        log("No ```python3 found!", Kind.WARNING)
        # find the last two instances of ``` and extract the code
        index2 = output.rfind("```")
        index = output.rfind("```", 0, index2)
    else:
        # find the first instance of ``` after the index
        index2 = output.find("```", index + 1)

    # extract the code
    code = output[index + 10 : index2]
    # remove trailing new lines
    code = code.rstrip()

    log(code, Kind.GENERATOR, "extracted code")
    return code


def process_code(code) -> str:
    parsed = ast.parse(code)
    output = print_uclid5(parsed)
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
    return code
