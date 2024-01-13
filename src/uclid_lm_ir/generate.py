import ast
import inspect
import os

from .module import Module
from .printer import print_uclid5
from .utils import generator_log, llm_log


def get_api_description() -> str:
    source = inspect.getsource(Module)
    index = source.find("def __str__")
    source = source[:index]
    # remove trailing new lines
    source = source.rstrip()
    return source


def get_prompt(task) -> str:
    """Returns the prompt for the GPT-4 API."""

    generator_log("Getting prompt...")

    if task.endswith("."):
        task = task[:-1]

    prompt = "Extend the `Module` class below to complete the following task:"
    prompt += " " + task + ". Reply with your code inside one unique code block."
    module_class = "```python3\n" + get_api_description() + "\n```\n"
    prompt += f"\n\n{module_class}\n```python3\n#TODO\n"

    generator_log("Prompt:", prompt)

    return prompt


def extract_code(output) -> str:
    """Extracts the code from the GPT-4 API response."""
    generator_log("Extracting code...")

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

    generator_log("Code:", code)
    return code


def process_code(code) -> str:
    """Processes the code to remove unwanted lines."""
    generator_log("Processing code...")

    parsed = ast.parse(code)
    # extract all the classes and nothing else
    parsed.body = [node for node in parsed.body if isinstance(node, ast.ClassDef)]
    output = print_uclid5(parsed)
    # remove empty lines
    output = "\n".join([line for line in output.split("\n") if line.strip()])

    generator_log("Processed code:", output)
    return output


def sketch_api(task, engine="gpt-4-0613"):
    """Generates code for a given task using the GPT-4 API."""
    generator_log("Generating code...")

    import openai

    openai.api_key = os.environ["OPENAI_API_KEY"]

    prompt = get_prompt(task)

    response = openai.ChatCompletion.create(
        model=engine, messages=[{"role": "user", "content": prompt}]
    )
    response = response["choices"][0]["message"]["content"]
    llm_log("Response:", response)

    code = extract_code(response)
    code = process_code(code)
    return code


def complete_api(code_with_holes, engine="gpt-4-0613") -> str:
    """Ask the llm to remove the question marks."""
    generator_log("Asking the llm to remove the question marks...")

    import openai

    openai.api_key = os.environ["OPENAI_API_KEY"]

    if "??" not in code_with_holes:
        return code_with_holes

    prompt = "Fix the UCLID5 code below by replacing every occurrence of `??` "
    prompt += f"with the correct value:\n```uclid5\n{code_with_holes}\n```\n"
    response = openai.ChatCompletion.create(
        model=engine, messages=[{"role": "user", "content": prompt}]
    )
    response = response["choices"][0]["message"]["content"]
    llm_log("Response:", response)
    code_with_holes = extract_code(response)
    return code_with_holes
