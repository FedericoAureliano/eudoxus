import functools
import re
import subprocess
from collections import Counter

from pydantic import BaseModel
from rich.console import Console
from rich.panel import Panel

from eudoxus.llm.gpt import chat_constrained, rewrite_module_with_llm_bmc

console = Console()
GENERATOR_STYLE = "blue"
LLM_STYLE = "bold magenta"
# UCLID_STYLE = "green"


def foldl(func, acc, xs):
    return functools.reduce(func, xs, acc)


def generator_log(*messages):
    """Logs a message from the generator."""

    if len(messages) > 1:
        message = " ".join([str(m) for m in messages[1:]])
        message = Panel(message, title=":robot: " + messages[0], expand=False)
    else:
        message = ":robot: " + messages[0]

    console.log(
        message,
        style=GENERATOR_STYLE,
        markup=True,
        emoji=True,
        justify="full",
        highlight=False,
    )


def llm_log(*messages):
    """Logs a message from the llm."""
    if len(messages) > 1:
        message = " ".join([str(m) for m in messages[1:]])
        message = Panel(message, title=":brain: " + messages[0], expand=False)
    else:
        message = ":brain: " + messages[0]

    console.log(
        message,
        style=LLM_STYLE,
        markup=True,
        emoji=True,
        justify="full",
        highlight=False,
    )


def uclid_log(*messages, style="green"):
    """Logs a message from UCLID"""
    if style == "green":
        emoji = ":white_check_mark: "
    else:
        emoji = ":negative_squared_cross_mark: "
    if len(messages) > 1:
        message = " ".join([str(m) for m in messages[1:]])
        message = Panel(message, title=emoji + messages[0], expand=False)
    else:
        message = emoji + messages[0]

    console.log(
        message,
        style=style,
        markup=True,
        emoji=True,
        justify="full",
        highlight=False,
    )


def get_module_name(code):
    pattern = r"module\s+([a-zA-Z0-9_]+)\s*{"
    match = re.search(pattern, code)
    module_name = ""
    if match:
        module_name = match.group(1)

    return module_name


def filter_cex_to_desired_length(cex, last_n_steps):
    assert type(cex) == str, "cex is not a string, terminating early"
    cex_lines = cex.split("\n")
    cex_lines.reverse()
    final_filtered = []
    seen_steps = 0
    finding_cex = False
    for line in cex_lines:
        if not finding_cex:
            if "step #" in line:
                seen_steps += 1
            final_filtered.append(line)
            if seen_steps == last_n_steps:
                finding_cex = True
        else:
            if "cex for" in line:
                final_filtered.append(line)
    final_filtered.reverse()
    return "\n".join(final_filtered)


def filter_cex(uclid_output):
    # print("starting filtering")
    DESIRED_TRACE_LENGTH = 3
    filtered_cex = ""
    if "cex for" not in uclid_output:
        return filtered_cex
    cex_start_location = uclid_output.index("cex for")

    pass_fail_property_section = uclid_output[:cex_start_location]
    # Regex pattern to extract the property name
    matches = re.findall(
        r"failed -> v\s+(?:\[step #\d+\]\s+)?property (\w+) @",
        pass_fail_property_section,
    )

    # Count occurrences
    failure_counts = Counter(matches)

    # Print results
    for property_name, count in failure_counts.items():
        filtered_cex += f"{property_name}: {count} failures\n"

    cex_uclid_output = uclid_output[cex_start_location:]
    all_failed_invs = set(re.findall(r"property (.*?) @", cex_uclid_output))
    # print("all failed invs: ", all_failed_invs)
    found_invs = set()
    # isolate the property traces
    cex_uclid_output_lines = cex_uclid_output.split("\n")  # gets each line
    i, total_lines = 0, len(cex_uclid_output_lines)
    property_trace = ""
    interested_in_trace = True
    further_filtering = []
    while i < total_lines:
        line = cex_uclid_output_lines[i]
        match = re.search(r"property (.*?) @", line)
        # need to handle duplicates
        if match:
            if len(all_failed_invs) == len(found_invs):
                further_filtering.append(property_trace)
                break
            further_filtering.append(
                property_trace
            )  # first will be nothing, but subsequent will be the property traces
            property = match.group(1)
            if property in found_invs:
                interested_in_trace = (
                    False  # not interested in trace until next property
                )
                property_trace = ""
                i += 1
                continue

            found_invs.add(property)
            interested_in_trace = True
            property_trace = ""
        else:
            if not interested_in_trace:
                i += 1
                continue

        property_trace += line + "\n"
        i += 1

    if len(further_filtering) == 1:
        further_filtering.append(property_trace)

    for trace in further_filtering[1:]:
        filtered_cex += filter_cex_to_desired_length(trace, DESIRED_TRACE_LENGTH)

    # if we can't extract what we want then we should return the original
    if filtered_cex == "":
        return uclid_output
    return filtered_cex


def run_uclid(ucl_mod, task, py_mod, iterations=3, llm_call=False):
    """Run uclid
    ucl_mod: str - module in uclid
    task : Path - path to task description
    py_mod: str - module in python - used for the llm to propose a candidate bound
    iterations: int - desired iterations for uclid execution
    llm_call : bool - iterations set by llm judgement
    """
    uclid_passes = False
    module_name = get_module_name(ucl_mod)
    # print(new_contents)

    if "bmc(3)" in ucl_mod:
        if llm_call:
            with open(task, "r") as f:
                task_desc = f.read()
            module_as_ucl = rewrite_module_with_llm_bmc(task_desc, py_mod, ucl_mod)
        else:
            module_as_ucl = ucl_mod.replace("bmc(3)", f"bmc({iterations})")
    else:
        module_as_ucl = ucl_mod
        # print("new ucl module: ", module_as_ucl)

    new_file_loc = "testing.ucl"
    write_fd = open(new_file_loc, "w")
    write_fd.write(module_as_ucl)
    write_fd.close()

    # important to have uclid downloaded and in the path
    try:
        command = f"uclid {new_file_loc} -m {module_name}"
        # print("running: ", command)
        result = subprocess.run(
            command,
            shell=True,
            executable="/bin/bash",
            capture_output=True,
            text=True,
        )
        # Get the standard output
        stdout = result.stdout
        # Get the standard error (if any)
        error = result.stderr

        if error:
            stdout = "ERROR: " + error + stdout + "\n" + ucl_mod

        def extract_uclid_stats(log_output):
            failed = log_output.lower().count("failed ->")
            passed = log_output.lower().count("passed ->")

            return max(0, failed), max(0, passed)

        failed_assertions, passed_assertions = extract_uclid_stats(stdout)

        # if failed not in stdout lower then it defo passed
        # if failed is in stdout, there could be the case that it is \
        # saying `0 assertions failed` so we check that
        if (
            "failed" not in stdout.lower() or failed_assertions == 0
        ) and "error" not in stdout.lower():
            # print(f"failed assertions count: {failed_assertions} | \
            # 'failed' not in stdout: {'failed' not in stdout.lower()} \
            # | error: {'error' not in stdout.lower()}")
            uclid_passes = True

    except Exception as e:
        print("error: ", e)

    return passed_assertions, failed_assertions, stdout, uclid_passes


def run_smoke_testing(ucl_mod):
    new_file_loc = "testing.ucl"
    write_fd = open(new_file_loc, "w")
    write_fd.write(ucl_mod)
    write_fd.close()
    module_name = get_module_name(ucl_mod)
    warnings = 54321
    # SMOKE TESTING

    try:
        command = f"uclid {new_file_loc} -m {module_name} --smoke"
        # print("running: ", command)
        result = subprocess.run(
            command,
            shell=True,
            executable="/bin/bash",
            capture_output=True,
            text=True,
        )
        # Get the standard output
        stdout = result.stdout
        # Get the standard error (if any)
        error = result.stderr
        if "error on" in stdout:
            return warnings, stdout

        if error:
            stdout = "ERROR: " + error + stdout + "\n"
            return warnings, stdout

        def parse_smoke_output(uclid_log_):
            def parse_warning_line(warning_line):
                pattern = r"warning -> lines? (\d+)(?:-(\d+))?(?: are never run\.)?"

                def extract_ranges(warning_text):
                    match = re.search(pattern, warning_text)
                    if match:
                        start = int(match.group(1))
                        stop = int(match.group(2)) if match.group(2) else start
                        return (start, stop)
                    return None  # No match found

                return extract_ranges(warning_line)

            smoke_results_line_split = uclid_log_.lower().split("\n")

            line_ranges = []
            for line in smoke_results_line_split:
                if "warning -> " in line:
                    line_range = parse_warning_line(line)
                    line_ranges.append(line_range)

            return line_ranges

        uclid_log("SMOKE OUTPUT: ", stdout)
        line_range_list = parse_smoke_output(stdout)
        warnings = len(line_range_list)
        if len(line_range_list) != 0:
            uclid_lines = enumerate(ucl_mod.split("\n"))
            pattern = r"//(\d+)"
            unhit_line_ids = []
            for line_num, line in uclid_lines:
                for start, stop in line_range_list:
                    if start <= line_num + 1 <= stop:
                        match = re.findall(pattern, line)
                        if match:
                            line_id = match[0]
                            unhit_line_ids.append(line_id)

            unhit_line_string = ", ".join(unhit_line_ids)
            final_smoke_cex = (
                "Lines with id: "
                + unhit_line_string
                + " are unreachable. The logic may be incorrect."
            )
        else:
            print(
                "There are no unreachable lines...this is the best uclid module\
                      that we can create"
            )
            final_smoke_cex = ""
        return warnings, final_smoke_cex

    except Exception as e:
        return 100, f"e: {e}"


def insert_string(original_string, insert_string, index):
    return original_string[:index] + insert_string + original_string[index:]


def insert_block_fixes(func_def_str, syntatic_correct_py_code, fix):
    block_delimited = func_def_str
    if block_delimited in syntatic_correct_py_code:
        block_location = syntatic_correct_py_code.index(block_delimited)
        syntatic_correct_py_code = insert_string(
            syntatic_correct_py_code,
            f"\n    #TODO: {fix}\n    ??",
            block_location + len(block_delimited),
        )
    else:
        syntatic_correct_py_code += f"   {func_def_str}\n"
        syntatic_correct_py_code += f"       #{fix}"
        syntatic_correct_py_code += "       ??"

    return syntatic_correct_py_code


def add_control_block(ucl_mod):
    """
    Adds a control block to a uclid module if it doesn't already exist
    """
    if "control {" in ucl_mod or "control  {" in ucl_mod or "print_results;" in ucl_mod:
        return ucl_mod
    else:
        last_closing_paren_index = ucl_mod.rfind("}")
        if last_closing_paren_index == -1:
            print("something is broken with the uclid module")
            return ucl_mod
        else:
            control_block = "  control {\n"
            control_block += "      v = bmc(3);\n"
            control_block += "      check;\n"
            control_block += "      print_results;\n  }\n"
            ucl_mod = insert_string(ucl_mod, control_block, last_closing_paren_index)
            return ucl_mod


def change_model(
    nm_pass,
    nm_fail,
    nm_uclid_pass,
    nm_warnings,
    best_model_info_dict,
    use_bmc,
    use_smoke,
):
    """
    compares two models and returns True if the new model is better than
    the best one yet, both need to be passed in.
    Input:
    nm_pass               : (int) - number of passed assertions of New Model
    nm_fail               : (int) - number of failed assertions of New Model
    nm_uclid_pass         : (bool) - whether or not uclid passed of New Model
    nm_warnings           : (int) - number of warnings (unreachable lines) of New Model
    best_model_info_dict  : (dict) - mapping of the previous values from best model yet
    use_bmc               : (bool) - whether or not we are running bmc
    use_smoke             : (bool) - whether or not we are running smoke

    Output:
    (bool) - True if new model is better, False if the old model performed better
    """
    # base case, first time and do not have anything populated
    if not best_model_info_dict["model"]:
        print("BASE CASE: NEED TO INITIALIZE THE NEW MODEL")
        return True

    _, old_fail, _, old_warnings = (
        best_model_info_dict["passed_assertions"],
        best_model_info_dict["failed_assertions"],
        best_model_info_dict["uclid_passes"],
        best_model_info_dict["warnings"],
    )

    if use_bmc and use_smoke:
        if not nm_uclid_pass:
            return False
        elif nm_fail > old_fail:
            return False
        elif nm_warnings > old_warnings:
            return False
    elif use_bmc:
        if nm_fail > old_fail:
            return False
    elif use_smoke:
        if nm_warnings > old_warnings:
            return False

    return True


def get_smoke_error_fixes(model, unhit_lines, nl_desc):
    class Suggestion(BaseModel):
        block: str
        description: str

    class SuggestionList(BaseModel):
        suggestions: list[Suggestion]

    prompt = """You are a formal methods specialist analyzing an imperfect model. \
        Your task\
        is to find the line numbers with the ids that I pass to you and analyze why \
            they are not being run.\n
        Then you have to determine if these unreachable lines are negatively impacting\
              the correctness of the \
            model. Finally if there is something incorrect, then provide suggestions\
                  on what needs to be fixed. \
                Follow this analysis framework:
a) Analyze the next function and determine if there is a major logic problem present.
b) Analyze the initialized values for any missing values or inconsistencies against\
      the specification.

Function DEFINITIONS:
locals - variable type declarations, DO NOT INITIALIZE ANY VARIABLE VALUES
init - variable value initialization
next - transition logic
specification - invariants that represent correct program execution

Focus exclusively on preceding the function definitions."""

    prompt += f"\n\nORIGINAL TASK DESCRIPTION:\n{nl_desc}"
    prompt += f"\n\nGENERATED PYTHON MODEL:\n{model}"
    prompt += f"\n\nUNREACHABLE LINE IDS:\n{unhit_lines}"

    user_prompt = "Understand why the provided line ids are not being reached, \
        and provide suggestions for how to fix the code to \
        be aligned with the provided task."

    summary = chat_constrained(prompt, user_prompt, SuggestionList)

    return [(f.block, f.description) for f in summary.suggestions]


def get_bmc_error_fixes(model, error_message, nl_desc):
    class Fix(BaseModel):
        block: str
        description: str
        related_cex: str

    class FixList(BaseModel):
        fixes: list[Fix]

    prompt = """You are a formal methods specialist analyzing failed \
        verification attempts. Your task is to:
1. Compare variable values to the specifications.
2. Identify why the generated PYTHON model failed to satisfy specifications.
3. Provide concise and specific fixes.

Follow this analysis framework:
a) Analyze the specification function and determine if there\
      is a major problem present.
b) Analyze the initialized values for any missing values or\
      inconsistencies against the specification.
c) Compare the logic in the python code to the task and assert that\
      basic transitions are present in the code.

Function DEFINITIONS:
locals - variable type declarations, DO NOT INITIALIZE ANY VARIABLE VALUES
init - variable value initialization
next - transition logic
specification - invariants that represent correct program execution

Focus exclusively on preceding the function definitions. \
    DO NOT RETURN ANY PYTHON CODE"""

    prompt += f"\n\nORIGINAL TASK DESCRIPTION:\n{nl_desc}"
    prompt += f"\n\nGENERATED PYTHON MODEL:\n{model}"
    prompt += f"\n\nVERIFICATION FAILURE ANALYSIS:\n{error_message}"

    error_message_split = error_message.lower().split("\n")
    init_ = 0
    logic = 0
    for e_m in error_message_split:
        if "failed ->" in e_m:
            if "step #0" in e_m:
                init_ += 1
            else:
                logic += 1

    if init_ > logic:
        user_prompt = """Using the failed invariants in the error message\
              and cross referencing with\
              the specification, provides concrete fixes to the code,\
                  focusing mostly on the variable\
                  initialization and then the program logic."""
    else:
        user_prompt = """Using the failed invariants in the error message\
              and cross referencing with \
              the specification, provides concrete fixes to the code,\
                  focusing on making sure the\
                  logic is correct and all variables are properly set and updated."""

    llm_log(
        "PROMPT FOR BMC SUMMARIZING ERROR MESSAGE: ",
        "SYSTEM PROMPT: \n" + prompt + "\nUSER PROMPT:\n" + user_prompt,
    )
    summary = chat_constrained(prompt, user_prompt, FixList)

    return [(f.block, f.description) for f in summary.fixes]
