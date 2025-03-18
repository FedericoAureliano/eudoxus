import inspect

from pydantic import BaseModel

from eudoxus.llm.gpt import chat_constrained


def get_api_description(spec, change_spec_loc, specless, aug_dsl) -> str:
    # TODO maybe rename vanilla to be default?
    if specless or aug_dsl:
        from eudoxus.llm.dsl_specless import Module
    elif change_spec_loc:
        from eudoxus.llm.dsl_rearrange_spec import Module
    elif spec == "no-involvement":
        from eudoxus.llm.dsl_default import Module
    else:
        from eudoxus.llm.dsl_force_spec import Module

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

    # invariant_per_var = chat_constrained("Give me one invariant per variable\
    #  defined in the following code block. ", specless_code, InvPairList) #exp26
    # invariant_per_var = chat_constrained("Give me one logical test per\
    #  variable defined in the following code block. ", specless_code, InvPairList) \
    # #exp27
    # invariant_per_var = chat_constrained(f"For the following task, give me\
    #  one logical  per variable defined in the following code block. Task: {task}"\
    # , specless_code, InvPairList) #exp27
    # invariant_per_var = chat_constrained(f"Adhering to the following task \
    # semantics, give me one invariant per variable defined in the following \
    # code block. Task: {task}", specless_code, InvPairList) #exp27
    # invariant_per_var = chat_constrained(f"Adhering to the following task \
    # semantics, give me one invariant that will hold for all executions per\
    #  variable defined in the following code block. Task: {task}\n", \
    # f"Code:\n {specless_code}", InvPairList) #exp27
    invariant_per_var = chat_constrained(
        f"Given the following task semantics, generate an invariant that holds\
              for all executions of each variable defined in the provided\
                  code block. Ensure that the invariant is logically valid\
                      and adheres strictly to the given semantics.\n\n \
                        Task Semantics: {task}\n",
        f"Code:\n {specless_code}",
        InvPairList,
    )  # exp27
    # invariant_per_var = chat_constrained("For each variable defined \
    # in the following code block, give me one propositional logic \
    # invariant. ", specless_code, InvPairList)
    # invariant_per_var = chat_constrained("For each variable defined \
    # in the following code block, write one propositional logic \
    # invariant. ", specless_code, InvPairList)
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
        remaining = specless_code[spec_start + len(delimiter) :].lower()
        middle = ""
        for inv_pair in invariant_per_var.inv_pair_list:
            var_name = inv_pair.variable_name.lower()
            var_inv = inv_pair.invariant_expr
            if (
                var_name not in remaining
                or f"self.{var_name} = ??" in remaining
                or f"self.{var_name}_inv = ??" in remaining
            ):
                print(f"either did not find {var_name} or it is now empty")
                middle += f"    # {var_inv} in prop logic looks like: \n"
                if "self" in var_name:
                    middle += f"    {var_name}_inv = ??\n"
                else:
                    middle += f"    self.{var_name}_inv = ??\n"

        print("beginning: ", specless_code[: spec_start + len(delimiter)])
        print("middle: ", middle)
        print("end: ", specless_code[spec_start + len(delimiter) :])

        return (
            specless_code[: spec_start + len(delimiter)]
            + "\n"
            + middle
            + specless_code[spec_start + len(delimiter) :]
        )


def augment_api_description(specless_code):
    orig_specless_api_desc = get_api_description(False, False, True, True)
    # print("specless code: ")
    # print(specless_code)
    # print("----- INV PER VAR ------")
    # print(invariant_per_var)

    # new_spec_code += "        \"\"\"(Optional) Defines the specification\
    #  in terms of invariant properties.\n"
    # new_spec_code += "        Returns:\n "
    # new_spec_code += "         bool: True if the specification is \
    # satisfied, False otherwise.\n "
    # new_spec_code += "        For example, the following implementation \
    # defines two invariants:\n"
    # new_spec_code += "        ```\n"
    # new_spec_code += "         def specification(self):\n"
    # new_spec_code += "             return self.x < 10 and self.y > 0\n"
    # new_spec_code += "        ```\n"

    # return_expr = gen_spec_block(specless_code)

    # new_spec_code += return_expr

    # print("new_spec_code: ", new_spec_code)
    # print("-------- FINAL NEW 'INCOMPLETE' API --------")
    # print(orig_specless_api_desc + "\n" + new_spec_code)
    # list_of_inv = "\n".join([f"[Invariant {i+1}] " + s.invariant for i, s in
    # enumerate(invariant_per_var.inv_pair_list)])
    new_spec_code = ""
    return orig_specless_api_desc + "\n" + new_spec_code


def get_sketch_prompt(task, add_specs, change_spec_loc, spec_loop, aug_dsl) -> str:
    """Returns the sketch prompt."""

    if task.endswith("."):
        task = task[:-1]

    prompt = "Write Python code that extends the `Module` class below"
    prompt += " to complete the following task.\n\n"
    if add_specs == "simple":
        prompt += " If the task does not describe specifications, please think of \
            some and add them. "
        prompt += "These specifications need to capture properties about the system. "
        prompt += "Do not return True!\n\n"
    prompt += "> " + task.replace("\n", " ").replace("\r", " ").replace("  ", " ")
    prompt = prompt.rstrip()
    if prompt.endswith("."):
        prompt = prompt[:-1]
    prompt += ".\n\nReply with your Python code inside one unique code block."
    module_class = (
        "```python\n"
        + get_api_description(add_specs, change_spec_loc, spec_loop, aug_dsl)
        + "\n```\n"
    )
    prompt += f"\n\n{module_class}\n"
    prompt += "I can definitely do that! Here is the Python code:\n"
    prompt += "```python\n"

    return prompt


def get_complete_prompt(
    code_with_holes: str,
    task: str,
    use_original: bool,
    semantic_assistance: str,
    change_spec_loc: bool,
    spec_loop: bool,
    aug_dsl: bool,
) -> str:
    """Returns the repair prompt."""
    if task.endswith("."):
        task = task[:-1]

    prompt = ""

    prompt += "\nFix the following Python code by replacing every occurrence of `??` "
    prompt += "with the correct code."
    if semantic_assistance == "simple":
        prompt += "\n Ensure that the specification block is defined and \
            contains boolean logic invariants. "
        prompt += "These invariants need to capture properties about the system. "
        prompt += "Do not just return True!\n\n"
    if aug_dsl:
        code_with_holes = gen_spec_block(code_with_holes, task)
        # code_with_holes += gen_spec_block(code_with_holes)
    prompt += f"\n```python\n{code_with_holes}\n```\n"
    prompt += "Make sure that your code extends the `Module` class below"

    if use_original:
        prompt += " and that it completes the following task.\n\n"
        prompt += "> " + task.replace("\n", " ").replace("\r", " ").replace("  ", " ")
        prompt = prompt.rstrip()

    if prompt.endswith("."):
        prompt = prompt[:-1]

    prompt += ".\n\nReply with your Python code inside one unique code block."
    # if not aug_dsl:
    #     module_class = "```python\n" +
    # get_api_description(semantic_assistance, change_spec_loc, spec_loop) + "\n```\n"
    # else:
    #     module_class = "```python\n" + augment_api_description\
    # (code_with_holes) + "\n```\n"
    semantic_assistance = "force"
    module_class = (
        "```python\n"
        + get_api_description(
            semantic_assistance, change_spec_loc, spec_loop, aug_dsl=False
        )
        + "\n```\n"
    )
    prompt += f"\n\n{module_class}\n"
    prompt += "I can definitely do that! Here is the fixed Python code:\n"
    prompt += "```python\n"

    return prompt


def get_spec_complete_prompt(syntax_good_code: str, task: str, specs: str):
    prompt = f"Below is the complete code for a defined module. Please \
        implement a specification block based on the following specification \
            suggestions:\n {specs}"

    prompt += "Do not change the existing code, but add a new specification\
          method so that the new specification method is syntactically correct\
              and reflects these suggestions. \n"
    prompt += "Using the variables defined already, you are only allowed \
        to use a combination of the following operators: \n"
    prompt += "bv, not, neg, and, or, xor, implies, iff, equal, add, sub, \
        mul, div, mod, neq, lt, le,  gt, ge, select, ite, random\n"
    prompt += "Make sure to return the entire updated module, not just the \
        modified specification block.\n"
    prompt += f"{syntax_good_code}"
    return prompt


def get_spec_complete_prompt_3(syntax_good_code: str, task: str, specs: str):
    prompt = f"Below is the complete code for a defined module. I want to\
          update the specification method based on the following specification\
              suggestions:\n {specs}"

    prompt += "\nPlease modify the code so that the new specification method\
          is syntactically correct and reflects these suggestions. \n"
    prompt += "Make sure to return the entire updated module, not just the \
        modified specification block.\n"
    prompt += f"{syntax_good_code}"
    return prompt


def get_spec_complete_prompt_2(syntax_good_code: str, task: str, specs: str):
    """Returns the prompt for just fixing the specification block."""
    prompt = ""
    prompt += (
        "Modify only the `def specification(self)` block in the following Python code. "
    )
    prompt += "Do not alter any other part of the code.\n\n"
    prompt += f"Ensure that the `specification` function encodes the \
        following specs using ONLY PROPOSITIONAL LOGIC:\n{specs}\n\n"
    prompt += "Here is the existing code:\n"
    prompt += f"```python\n{syntax_good_code}\n```\n"
    prompt += "Return the updated Python code in a single code block without \
        additional formatting, keeping all original code intact except for \
            `specification`.\n"

    return prompt


def get_spec_complete_prompt_1(syntax_good_code: str, task: str, specs: str):
    """returns the prompt for just fixing the specification block"""
    prompt = ""
    prompt += "\nModify only the `def specification(self)` block in the following \
        Python code. Do not alter any other part of the code. "
    prompt += f"Make sure that the specification blocks is an encoding of the \
          following specs ONLY IN PROPOSITIONAL LOGIC: {specs}\n"
    prompt += "Return the updated simple Python code in a single code block, \
        keeping all original code intact except for the `specification` function."
    prompt += f"\n```python\n{syntax_good_code}\n```\n"
    prompt += "Make sure that your code keeps the above and only changes \
          the specification function. "
    prompt += "\n\nReply with your Python code inside one unique code block.\n"
    prompt += "I can definitely do that! Here is the fixed Python code:\n"
    # prompt += "Don't change anything except the specification function."

    return prompt
