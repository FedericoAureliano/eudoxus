import inspect

from eudoxus.llm.dsl import Module


def get_api_description() -> str:
    source = inspect.getsource(Module)
    index = source.find("def __str__")
    source = source[:index]
    # remove trailing new lines
    source = source.rstrip()
    return source


def get_sketch_prompt(task) -> str:
    """Returns the sketch prompt."""

    if task.endswith("."):
        task = task[:-1]

    prompt = "Write Python code that extends the `Module` class below"
    prompt += " to complete the following task:"
    prompt += " " + task + ". Reply with your Python code inside one unique code block."
    module_class = "```python3\n" + get_api_description() + "\n```\n"
    prompt += f"\n\n{module_class}\n```python3\n#TODO\n"

    return prompt


def extract_code(output) -> str:
    """Extracts the code from the LLM response."""

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

    return code


def get_complete_prompt(code_with_holes, original=None):
    """Returns the repair prompt."""
    prompt = ""

    if original:
        prompt += "\nFix the Python code below by replacing every occurrence of `??` "
        prompt += f"so that it accomplishes this task: {original}\n"
        prompt += f"```python\n{code_with_holes}\n```\n"
    else:
        prompt += "\nFix the Python code below by replacing every occurrence of `??` "
        prompt += f"with the correct code:\n```python\n{code_with_holes}\n```\n"

    return prompt
