import inspect
import os
import subprocess

import openai

from .module import Module

if "OPENAI_API_KEY" not in os.environ:
    openai.api_key = "NONE"
else:
    openai.api_key = os.environ["OPENAI_API_KEY"]


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
    return prompt


def extract_code(output) -> str:
    """Extracts the code from the GPT-4 API response."""
    # find the last instance of ```python3
    index = output.rfind("```python3")
    # find the first instance of ``` after the index
    index2 = output.find("```", index + 1)
    # extract the code
    code = output[index + 10 : index2]
    # remove trailing new lines
    code = code.rstrip()
    return code


def process_code(code) -> str:
    index = code.find("class")
    index2 = code.find("(", index + 1)
    class_name = code[index + 6 : index2].strip()

    code = "from uclid_lm_ir import *\n" + code
    code += "\n\nprint(" + class_name + "())\n"

    # write the code to a temporary file
    with open("temp.py", "w") as f:
        f.write(code)
    # execute temp.py in a subprocess and capture the output
    output = subprocess.check_output(["python3", "temp.py"]).decode("utf-8")

    return output


def gpt4_write_code(task, engine="gpt-4-0613"):
    """Generates code for a given task using the GPT-4 API."""
    prompt = get_prompt(task)
    response = openai.ChatCompletion.create(
        model=engine, messages=[{"role": "user", "content": prompt}]
    )
    response = response["choices"][0]["message"]["content"]
    code = extract_code(response)
    code = process_code(code)
    return code
