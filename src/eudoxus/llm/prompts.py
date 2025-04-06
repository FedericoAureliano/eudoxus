import inspect

from pydantic import BaseModel

from eudoxus.llm.gpt import chat_constrained


def get_api_description(spec_format) -> str:
    if spec_format == "specless":
        from eudoxus.llm.dsl_specless import Module
    elif spec_format == "force_spec":
        from eudoxus.llm.dsl_force_spec import Module
    else:
        from eudoxus.llm.dsl_default import Module

    source = inspect.getsource(Module)
    index = source.find("def __str__")
    source = source[:index]
    # remove trailing new lines
    source = source.rstrip()

    return source


def gen_spec_block(specless_code, task):
    """TODO: Need to change the variable name and the function name
    generates the spec block to put into the code. In the first \
        iteration we want to add it for all of them.

    Returns: new_spec_code = original_code_with_holes + altered_spec_block"""

    class Pair(BaseModel):
        variable_name: str
        invariant_expr: str

    class InvPairList(BaseModel):
        inv_pair_list: list[Pair]

    invariant_per_var = chat_constrained(
        f"Given the following task semantics, generate an invariant that holds\
              for all executions of each variable defined in the provided\
                  code block. Ensure that the invariant is logically valid\
                      and adheres strictly to the given semantics.\n\n \
                        Task Semantics: {task}\n",
        f"Code:\n {specless_code}",
        InvPairList,
    )

    delimiter = "def specification(self):"
    if delimiter not in specless_code:
        new_spec_code = "  def specification(self):\n"
        return_expr = "      return and("
        for inv_pair in invariant_per_var.inv_pair_list:
            new_spec_code += (
                f"    #{inv_pair.invariant_expr} in prop logic looks like: \n"
            )
            # formatting in case llm gives the variable name with `self.`
            if "self." in inv_pair.variable_name:
                new_spec_code += f"    {inv_pair.variable_name}_inv = ??\n"
                return_expr += f"{inv_pair.variable_name},"
            else:
                new_spec_code += f"    self.{inv_pair.variable_name}_inv = ??\n"
                return_expr += f"self.{inv_pair.variable_name},"

        # need to remove the last comma, and replace it with a closing paren
        return_expr = return_expr[:-1]
        return_expr += ")"
        # return new_spec_code + return_expr

        return_expr = (
            "    # return expression should combine all previous invariants together\n"
        )
        return_expr += "    return ??\n"
        return specless_code + new_spec_code + return_expr
    else:
        spec_start = specless_code.index(delimiter)
        check_against = specless_code[spec_start + len(delimiter) :].lower()
        remaining = specless_code[spec_start + len(delimiter) :]
        middle = ""
        for inv_pair in invariant_per_var.inv_pair_list:
            var_name = inv_pair.variable_name.lower()
            var_inv = inv_pair.invariant_expr
            if (  # this should be and or of two andss
                (f"{var_name} = " not in check_against)
                and (f"{var_name}_inv = " not in check_against)
                or (
                    f"self.{var_name} = ??" in check_against
                    or f"self.{var_name}_inv = ??" in check_against
                )
            ):
                if f"self.{var_name} = ??" in check_against:
                    remaining = remaining.replace(f"self.{var_name} = ??", "")
                if f"self.{var_name}_inv = ??" in check_against:
                    remaining = remaining.replace(f"self.{var_name}_inv = ??", "")
                print(f"either did not find {var_name} or it is now empty")
                middle += f"    # {var_inv} in prop logic looks like: \n"
                if "self" in var_name:
                    if "_inv" in var_name:
                        middle += f"    {var_name} = ??\n"
                    else:
                        middle += f"    {var_name}_inv = ??\n"
                else:
                    if "_inv" in var_name:
                        middle += f"    self.{var_name} = ??\n"
                    else:
                        middle += f"    self.{var_name}_inv = ??\n"

        return specless_code[: spec_start + len(delimiter)] + "\n" + middle + remaining


def get_sketch_prompt(task, spec_format="default") -> str:
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
    module_class = "```python\n" + get_api_description(spec_format) + "\n```\n"
    prompt += f"\n\n{module_class}\n"
    prompt += "I can definitely do that! Here is the Python code:\n"
    prompt += "```python\n"

    return prompt


def get_feedback_complete_prmpt(task, incorrect_code, fix):
    """Returns the prompt used for prompting LLM to take feedback"""
    print(fix)

    prompt = "Fix the following Python code by doing two things\
          according to the fixes in the appropriate functions."
    prompt += f"Task: \n{task}\n"
    prompt += f"Incorrect Code: \n{incorrect_code}\n"
    prompt += "Desired Fixes: \n"
    prompt += fix
    prompt += "\n"
    # prompt += f"Desired Fixes: {formatted_fix}"

    prompt += "\nReply with your Python code inside one unique code block.\n"
    prompt += "I can definitely do that! Here is the Python code:\n"
    prompt += "```python\n"

    return prompt


def get_complete_prompt(
    code_with_holes: str,
    task: str,
    use_original: bool,
    spec_format: str,
) -> str:
    """Returns the repair prompt."""
    if task.endswith("."):
        task = task[:-1]

    prompt = ""

    prompt += "\nFix the following Python code by replacing every occurrence of `??` "
    prompt += "with the correct code."

    if spec_format != "default":
        code_with_holes = gen_spec_block(code_with_holes, task)

    # we pass in code_with_holes anyways so this is fine
    prompt += f"\n```python\n{code_with_holes}\n```\n"
    prompt += "Make sure that your code extends the `Module` class below"

    if use_original:
        prompt += " and that it completes the following task.\n\n"
        prompt += "> " + task.replace("\n", " ").replace("\r", " ").replace("  ", " ")
        prompt = prompt.rstrip()

    if prompt.endswith("."):
        prompt = prompt[:-1]

    prompt += ".\n\nReply with your Python code inside one unique code block."

    module_class = "```python\n" + get_api_description(spec_format) + "\n```\n"
    prompt += f"\n\n{module_class}\n"
    prompt += "I can definitely do that! Here is the fixed Python code:\n"
    prompt += "```python\n"

    return prompt
