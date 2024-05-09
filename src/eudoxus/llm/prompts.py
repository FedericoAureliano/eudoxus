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
    prompt += " to complete the following task.\n\n"
    prompt += "> " + task.replace("\n", " ").replace("\r", " ").replace("  ", " ")
    prompt = prompt.rstrip()
    if prompt.endswith("."):
        prompt = prompt[:-1]
    prompt += ".\n\nReply with your Python code inside one unique code block."
    module_class = "```python\n" + get_api_description() + "\n```\n"
    prompt += f"\n\n{module_class}\n"
    prompt += "I can definitely do that! Here is the Python code:\n"
    prompt += "```python\n"

    return prompt


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
