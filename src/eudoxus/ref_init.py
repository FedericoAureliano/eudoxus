import csv
import os
import re
import subprocess
import sys
import time
from datetime import datetime
from enum import Enum
from io import StringIO
from pathlib import Path

import typer
from pydantic import BaseModel
from typing_extensions import Annotated

from eudoxus.emit.python import module2py
from eudoxus.emit.uclid import module2ucl
from eudoxus.llm.gpt import chat, chat_constrained
from eudoxus.llm.prompts import get_complete_prompt, get_sketch_prompt
from eudoxus.llm.utils import extract_code
from eudoxus.parse.python import Parser
from eudoxus.repair.cycle import CycleChecker
from eudoxus.repair.declared import DeclaredChecker
from eudoxus.repair.duplicate import DuplicateChecker
from eudoxus.repair.input import InputChecker
from eudoxus.repair.instance import InstanceChecker
from eudoxus.repair.locals import LocalChecker
from eudoxus.repair.nondet import NondetChecker
from eudoxus.repair.quantifier import QuantifierChecker
from eudoxus.repair.scope import ScopeChecker
from eudoxus.repair.select import SelectChecker
from eudoxus.repair.type import TypeChecker
from eudoxus.rewrite import Rewriter
from eudoxus.utils import generator_log, llm_log, uclid_log


class Language(str, Enum):
    python = "python"
    uclid = "uclid"


class Model(str, Enum):
    gpt4 = "gpt-4-turbo-2024-04-09"
    gpt35 = "gpt-3.5-turbo-0125"


class SemanticInvolvement(str, Enum):
    vanilla = "no-involvement"
    simple = "simple"
    external_llm = "external-llm"


eudoxus = typer.Typer(pretty_exceptions_enable=False, add_completion=False)
CSV_LOC = "results.csv"


@eudoxus.command()
def main_(
    task: Path,
    language: Language = Language.uclid,
    model: Model = Model.gpt35,
    output: Path = None,
    iterations: int = 2,
    sem_iters: int = 3,
    inference: bool = True,
    remind: bool = True,
    solver: Annotated[bool, typer.Option(hidden=True)] = True,
    debug: Annotated[bool, typer.Option(hidden=True)] = False,
    semantic_assistance: SemanticInvolvement = SemanticInvolvement.vanilla,
    verf_eng_feedback: bool = False,
    to_csv: bool = False,
    constrained_decode: bool = False,
    change_spec_loc: bool = False,
    spec_loop: bool = False,
) -> None:
    if output is None:
        output = sys.stdout
    else:
        extension = output.suffix
        if extension == ".py" and language != Language.python:
            print("Language and output file extension do not match!")
            return
        if extension == ".ucl" and language != Language.uclid:
            print("Language and output file extension do not match!")
            return
        output = open(output, "w")

    # in the case of code repair, you don't want semantic assistance
    if iterations < 1:
        syntax_pipeline(
            task,
            language,
            model,
            output,
            inference,
            iterations,
            debug,
            remind,
            solver,
            semantic_assistance,
            constrained_decode,
            change_spec_loc,
            spec_loop,
        )
        if output is not sys.stdout:
            output.close()
    else:
        # initialize the csv
        if to_csv:
            if CSV_LOC not in os.listdir():
                with open(CSV_LOC, "w", newline="") as file:
                    writer = csv.writer(file)
                    writer.writerow(
                        [
                            "task",
                            "date",
                            "semantic assistance",
                            "suggestions",
                            "invariants",
                            "constr_decode",
                            "passed_assertions",
                            "failed_assertions",
                            "original_lines",
                            "final_lines",
                            "llm_calls",
                            "llm_time",
                            "repair_time",
                            "Spec Defined",
                            "Exit Cause",
                            "output",
                        ]
                    )

        semantic_pipeline(
            task,
            language,
            model,
            output,
            inference,
            iterations,
            debug,
            remind,
            solver,
            semantic_assistance,
            verf_eng_feedback,
            to_csv,
            constrained_decode,
            change_spec_loc,
            sem_iters,
            spec_loop,
        )
        if output is not sys.stdout:
            # print("going to close the output")
            output.close()


def semantic_pipeline(
    task,
    language,
    model,
    output,
    inference,
    iterations,
    debug,
    remind,
    solver,
    semantic_assistance,
    verf_eng_feedback,
    to_csv,
    constr_decode,
    change_spec_loc,
    sem_iters,
    spec_loop,
):
    # MAX_SEM_ITER = 2
    MAX_SEM_ITER = sem_iters

    sem_iter = 1
    UCL_LOC = "testing.ucl"
    BASE_TASK_LOC = task
    id = datetime.now()

    # print("hello from semantic pipeline")
    # do-while loop
    all_stats = []
    while True:
        # through each iteration through the syntactic - semantic pipeline,
        # uclid_passes needs to start off as false or we will take the value
        #  from the previous iteration which might have passed uclid, but
        # not had a specification block defined
        uclid_passes = False
        spec_defined = False
        failed_assertions = 0
        passed_assertions = 0
        semantic_stats = f"  SEMANTIC ITERATION {sem_iter}\n"
        print("semantic iteration: ", sem_iter)
        syntatic_correct_py_code, stats, stat_dict = syntax_pipeline(
            task,
            language,
            model,
            output,
            inference,
            iterations,
            debug,
            remind,
            solver,
            semantic_assistance,
            constr_decode,
            change_spec_loc,
            spec_loop,
        )
        original_lines = stat_dict["original_lines"]
        final_lines = stat_dict["final_lines"]
        llm_calls = stat_dict["llm_calls"]
        llm_time = stat_dict["llm_time"]
        repair_time = stat_dict["repair_time"]
        suggestions = stat_dict["suggestions"]
        gen_inv = stat_dict["gen_inv"]
        spec_defined = "def specification(self)" in syntatic_correct_py_code

        stats = semantic_stats + stats
        if not verf_eng_feedback:
            if to_csv:
                with open(CSV_LOC, "a+") as file:
                    writer = csv.writer(file)
                    writer.writerow(
                        [
                            BASE_TASK_LOC,
                            id,
                            semantic_assistance,
                            suggestions,
                            gen_inv,
                            constr_decode,
                            "N/A",
                            "N/A",
                            original_lines,
                            final_lines,
                            llm_calls,
                            llm_time,
                            repair_time,
                            spec_defined,
                            "user did not want verification",
                            output.name,
                        ]
                    )
            new_contents = syntatic_correct_py_code
            break

        # in the case that we are not giving feedback, we just want keep
        # the file open so that we can write to it outside the loop
        if output is not sys.stdout:
            # print("going to close the output")
            output.close()
        # print("syntatic correct py code: \n", syntatic_correct_py_code)
        # python code gets translated into uclid, cleaned up and then
        # written to a testing location
        # just for UCLID code, to encode the python into uclid and write
        #  it for uclid5 execution
        UCL_out_fd = open(UCL_LOC, "w")
        encoded_py_code = syntatic_correct_py_code.encode()
        modules = Parser(encoded_py_code).parse()
        # by this point, the module should have gone through all of the
        # associated checks
        # should not be holes
        modules = [m for m in modules if not m.is_empty()]
        for m in modules:
            module2ucl(UCL_out_fd, m, 0)
        UCL_out_fd.close()

        # open the file,
        read_fd = open(UCL_LOC, "r")
        # read the contents
        module_as_ucl = read_fd.read()
        # close the file
        read_fd.close()

        if "??" in module_as_ucl:
            print("found ?? in model, can't run uclid")
            stats += "Failed Assertions: N/A\n"
            stats += "Passed Assertions: N/A\n"
            all_stats.append(stats)
            if to_csv:
                with open(CSV_LOC, "a+") as file:
                    writer = csv.writer(file)
                    writer.writerow(
                        [
                            BASE_TASK_LOC,
                            id,
                            semantic_assistance,
                            suggestions,
                            gen_inv,
                            constr_decode,
                            "N/A",
                            "N/A",
                            original_lines,
                            final_lines,
                            llm_calls,
                            llm_time,
                            repair_time,
                            spec_defined,
                            "?? in model",
                            output.name,
                        ]
                    )
            continue

        new_contents = process_code(module_as_ucl)
        module_name = get_module_name(new_contents)
        # print(new_contents)

        new_file_loc = "testing.ucl"
        write_fd = open(new_file_loc, "w")
        write_fd.write(new_contents)
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
                stdout = "ERROR: " + error + stdout + "\n" + new_contents

            def extract_uclid_stats(log_output):
                # match = re.search(r"(\d+) assertions failed", log_output)
                # method_one = 0
                # if match:
                #     method_one = int(match.group(1))

                failed = log_output.lower().count("failed ->")
                passed = log_output.lower().count("passed ->")

                return max(0, failed), max(0, passed)

            failed_assertions, passed_assertions = extract_uclid_stats(stdout)

            style = "red"
            # if failed not in stdout lower then it defo passed
            # if failed is in stdout, there could be the case that it is \
            # saying `0 assertions failed` so we check that
            if (
                "failed" not in stdout.lower() or failed_assertions == 0
            ) and "error" not in stdout.lower():
                # print(f"failed assertions count: {failed_assertions} | \
                # 'failed' not in stdout: {'failed' not in stdout.lower()} \
                # | error: {'error' not in stdout.lower()}")
                style = "green"
                uclid_passes = True

            uclid_log("UCLID MODULE: ", module_as_ucl, style=style)
            uclid_log("Running UCLID Terminal Output: ", stdout, style=style)
        except Exception as e:
            print("error: ", e)

        stats += f"Failed Assertions:  {failed_assertions}\n"
        stats += f"Passed Assertions:  {passed_assertions}\n"
        stats += "-------------------\n"
        all_stats.append(stats)
        sem_iter += 1

        if to_csv:
            with open(CSV_LOC, "a+") as file:
                writer = csv.writer(file)
                writer.writerow(
                    [
                        BASE_TASK_LOC,
                        id,
                        semantic_assistance,
                        suggestions,
                        gen_inv,
                        constr_decode,
                        passed_assertions,
                        failed_assertions,
                        original_lines,
                        final_lines,
                        llm_calls,
                        llm_time,
                        repair_time,
                        spec_defined,
                        "no failures",
                        output.name,
                    ]
                )
        if sem_iter > MAX_SEM_ITER:
            break

        if uclid_passes:
            if spec_defined:
                # need to have uclid pass with a specification block
                print("uclid passed and we have a specification block defined")
                break
            else:
                stdout = "No specification block defined. Make sure the \
                    specifications represent the essence of the task description.\n"

        # if uclid doesn't pass, then there is already an error message to take\
        #  into consideration

        # get the base task from the location
        with open(BASE_TASK_LOC, "r") as f:
            task = f.read()

        if constr_decode:
            summarized_response = get_err_message_summary_constrained(
                syntatic_correct_py_code, stdout, task
            )
        else:
            summarized_response = get_err_message_summary(
                syntatic_correct_py_code, stdout, task
            )
        task += "\n" + summarized_response
        temp_write_loc = "temp.txt"
        with open(temp_write_loc, "w") as f:
            f.write(task)

        # task is supposed to be a file loc, so it needs to be updated after writing
        # we change the filepath to be temp_write_loc, because it will have \
        # the updated task material
        task = temp_write_loc

    if verf_eng_feedback:
        uclid_log("UCLID: ", module_as_ucl, style=style)
        print("uclid passed: ", uclid_passes)

    generator_log("Stats:", " ".join(all_stats))
    repair(new_contents, language, output, False, debug, solver)

    return


def return_with_valid_paren(code):
    stack = []
    open_locations = []
    for i in range(len(code)):
        c = code[i]
        if c == "(":
            stack.append(c)
        elif c == ")":
            if stack:
                stack.pop()
            else:
                open_locations.append(i)

    def insert_string(original_string, insert_string, index):
        return original_string[:index] + insert_string + original_string[index:]

    # hopefully you don't need this but in case, this is still kind of here
    # for insert_loc in open_locations:
    #     code = insert_string(code)

    if stack:
        for _ in stack:
            code += ")"

    return code


def filter_llm_response(llm_response):
    return llm_response
    delimiter = "def specification(self):"
    if delimiter in llm_response:
        spec_start = llm_response.index(delimiter)
        start = llm_response[:spec_start]
        remaining = llm_response[spec_start + len(delimiter) :]

        end_index = len(remaining)
        if "def " in remaining:
            end_index = remaining.index("def ")

        search_space = remaining[:end_index]

        spec_lines = search_space.split("\n")
        BANNED_WORDS = ["int", "bool", "self.int", "self.bool", "Boolean", "Integer"]
        filtered_spec = []
        for spec_line in spec_lines:
            # check for duplicates
            if "=" in spec_line:
                equals_op_loc = spec_line.index("=")
                lhs = spec_line[:equals_op_loc].strip()
                if f"{lhs} = {lhs}" in spec_line:
                    print("specline is the same thing repeated: ", spec_line)
                    continue

            # line_by_space = spec_line.split(" ")
            # if len(line_by_space) != len(set(line_by_space)):
            #     print(f"continued because the lengths of the list and set were\
            #  not the same| list: {line_by_space} | set: {set(line_by_space)}")
            #     continue
            good_word = True
            for banned_word in BANNED_WORDS:
                if banned_word in spec_line:
                    good_word = False
                    print("found banned word: " + banned_word + " in " + spec_line)
            if good_word:
                filtered_spec.append(spec_line)

        return start + delimiter + "\n ".join(filtered_spec)
    else:
        return llm_response


def syntax_pipeline(
    task,
    language,
    model,
    output,
    inference,
    iterations,
    debug,
    remind,
    solver,
    semantic_assistance,
    constr_decode,
    change_spec_loc,
    spec_loop,
):
    clocks = {"llm": 0, "repair": 0}

    def timeit(clock, f, *args, **kwargs):
        time1 = time.time()
        ret = f(*args, **kwargs)
        time2 = time.time()
        clocks[clock] += time2 - time1
        return ret

    # task is assumed to be a filepath
    with open(task, "r") as f:
        task = f.read()

    if iterations < 1:
        # assume task is a path to a file with code to repair
        repair(task, language, output, inference, debug, solver)
        return

    # [ANI] put an if check here in the case that you just want to update the python\
    #  code directly which would remove the following 16 lines
    # and you need to change teh get_complete_prompt
    # should be able to remove the below
    if semantic_assistance == SemanticInvolvement.external_llm:
        if constr_decode:
            task, specs = get_task_with_constrained_specs(task)
        else:
            task, specs = get_task_with_specs(task)
    prompt = get_sketch_prompt(
        task, semantic_assistance, change_spec_loc, spec_loop, True
    )  # could this also go into the semantic pipeline?
    generator_log("Prompt:", prompt)
    llm_response = timeit("llm", chat, prompt, model)
    # filter llm response
    llm_log("Original Response:", llm_response)
    llm_response = filter_llm_response(llm_response)
    # llm_log("Response:", llm_response)
    llm_log("Filtered Response:", llm_response)
    python = extract_code(llm_response)
    original = python
    generator_log("Extracted:", python)
    repaired = StringIO()
    timeit(
        "repair", repair, python, Language.python, repaired, inference, debug, solver
    )
    repaired = repaired.getvalue()
    # if "def spec" not in repaired:
    #     repaired += "\n def specification(self):\n"
    #     repaired += "       ??\n"
    generator_log("Repaired:", repaired)

    llm_calls = 1
    aug_dsl = True
    for _ in range(1, iterations):
        if "??" not in repaired and "def spec" in repaired:
            break
        # may need to change this prompt if you have the if check at 177
        prompt = get_complete_prompt(
            repaired,
            task,
            remind,
            semantic_assistance,
            change_spec_loc,
            spec_loop,
            aug_dsl,
        )
        generator_log("Prompt:", prompt)
        llm_response = timeit("llm", chat, prompt, model)
        llm_log("Original Response:", llm_response)
        llm_response = filter_llm_response(llm_response)
        llm_log("Filtered Response:", llm_response)
        python = extract_code(llm_response)
        generator_log("Extracted:", python)
        repaired = StringIO()
        timeit(
            "repair",
            repair,
            python,
            Language.python,
            repaired,
            inference,
            debug,
            solver,
        )
        repaired = repaired.getvalue()
        generator_log("Repaired:", repaired)
        llm_calls += 1

    # print("GOING TO RUN THE SPEC LOOP!")
    # spec_loop = True
    # if spec_loop:
    #     sem_loop_iter = 5
    #     _, specs = get_task_with_constrained_specs(task)
    #     llm_log("SPECS: ", specs)
    #     ran_loop = False
    #     for _ in range(1, sem_loop_iter):
    #         if "??" not in repaired and "return True" not in repaired and \
    # "def specification" in repaired and ran_loop:
    #             break
    #         prompt = get_spec_complete_prompt(repaired, task, specs)
    #         generator_log("Prompt:", prompt)
    #         llm_response = timeit("llm", chat, prompt, model)
    #         llm_log("Response:", llm_response)
    #         python = extract_code(llm_response)
    #         generator_log("Extracted:", python)
    #         repaired = StringIO()
    #         timeit("repair", repair, python, Language.python, repaired, \
    # inference, debug, solver,)
    #         repaired = repaired.getvalue()
    #         generator_log("Repaired:", repaired)
    #         ran_loop = True

    original_lines = len(original.splitlines())
    final_lines = len(repaired.splitlines())
    llm_time = round(clocks["llm"], 2)
    repair_time = round(clocks["repair"], 2)
    suggestions = extract_hints(task)
    gen_inv = extract_invariants(task)

    stats = f"Original Lines: {original_lines}\n"
    stats += f"Final Lines:    {final_lines}\n"
    stats += f"LLM Calls:      {llm_calls}\n"
    stats += f"LLM Time:       {llm_time}s\n"
    stats += f"Repair Time:    {repair_time}s\n"
    stats += f"Suggestions:     {suggestions}\n"
    stats += f"Gen. Inv:        {gen_inv}\n"
    generator_log("Stats:", stats)

    stats_as_dict = {
        "original_lines": original_lines,
        "final_lines": final_lines,
        "llm_calls": llm_calls,
        "llm_time": llm_time,
        "repair_time": repair_time,
        "suggestions": suggestions,
        "gen_inv": gen_inv,
    }

    # this is essentially used for printing to the correct associated file
    # repair(repaired, language, output, False, debug, solver)  # moved to the \
    # semantic pipeline because this is just used for printing

    return repaired, stats, stats_as_dict


def extract_hints(code):
    pattern = r"\[\w+\s\d+\]"
    matches = re.findall(pattern, code)
    return len(matches)


def extract_invariants(code):
    INVARIANT_DELIMITED = "make sure that you satisfy the following specifications"
    if INVARIANT_DELIMITED not in code.lower():
        return 0
    else:
        matches_one = 0
        matches_two = 0
        pattern_one = r"\d+\."
        matches_one = re.findall(pattern_one, code)

        pattern_two = r"\[Invariant \d+\]"
        matches_two = re.findall(pattern_two, code)
        return len(max(matches_one, matches_two))


def repair(src, language, output, inference, debug, solver):
    def write():
        if language == Language.python:
            for m in modules:
                # print("module to print: ", m)
                module2py(output, m, 0)

        if language == Language.uclid:
            for m in modules:
                module2ucl(output, m, 0)

    # check if src is a file path or the actual code
    if len(src) < 50 and Path(src).is_file():
        with open(src, "rb") as f:
            src = f.read()
    else:
        src_by_lines = src.split("\n")
        final_src_by_lines = []
        for line in src_by_lines:
            final_src_by_lines.append(return_with_valid_paren(line))
        # src = return_with_valid_paren(src)
        og_src_len = len(src)
        src = "\n".join(final_src_by_lines)

        if og_src_len != len(src):
            print("should have added a paren")
        src = src.encode()

    modules = Parser(src, debug).parse()
    # print("in repair")
    # print("modules: ", modules)
    # filter out any empty modules named Module
    modules = [m for m in modules if not m.is_empty()]

    if inference:
        checkers = [
            InputChecker,
            NondetChecker,
            InstanceChecker,
            SelectChecker,
            ScopeChecker,
            QuantifierChecker,
            LocalChecker,
            CycleChecker,
            DeclaredChecker,
            DuplicateChecker,
        ]
        # Type last: adds missing types using a MAX-SMT solver
        if solver:
            checkers.append(TypeChecker)
    else:
        checkers = []

    for checker in checkers:
        if checker == DeclaredChecker:
            rewrites, new_mods = checker().check(modules)
            modules = new_mods + modules
        else:
            rewrites = checker().check(modules)

        for rewrite in rewrites:
            rewriter = Rewriter(rewrite)
            modules = [rewriter.rewrite(m) for m in modules]

        # print(f"{len(modules)} checker: {checker}")
        # for m in modules:
        #     print("init when printing: ", m.init)

    write()


def get_task_with_specs(task):
    """ask an llm to come up with specs for task"""
    prompt = "You are an expert in formal methods, specializing in generating \
        system properties and specifications. Your task is to generate invariants\
              for a system based on its natural language description.\n"

    prompt += "Guidelines:\n \
    1. Invariants: Identify properties that must hold true in all states of the\
          system. These are conditions that are always true regardless of the \
            system's execution path.\n"

    prompt += "Input: \n \
        I will provide you with a natural language description of the system, \
            including: \n \
            * The components and their interactions. \
            * The desired behaviors of the system. \
            * Any constraints, safety, or performance requirements.\n"

    prompt += "Output: \n \
        * A list of invariants expressed in mathematical notation"

    prompt += task

    specs = chat(prompt, Model.gpt35)

    new_task = task
    new_task += "\n Make sure that you satisfy the following specifications: \n"
    new_task += specs

    return new_task, specs


def get_task_with_constrained_specs(task):
    # print("going to add specs to this task: ", task)
    """using constrained decoding, get an llm to come up with specs for the task"""

    class invariant(BaseModel):
        invariant: str
        task_mapping: str

    class invariantList(BaseModel):
        inv_list: list[invariant]

    prompt = "You are an expert in formal methods, specializing in generating \
        system properties and specifications. Your task is to generate a list of\
              simple invariants for a system based on its natural language \
                description.\n"

    prompt += "Guidelines:\n \
    1. Invariants: Identify simple properties that must hold true in all states\
          of the system. These are conditions that are always true regardless of\
              the system's execution path.\n"

    prompt += "Input: \n \
        I will provide you with a natural language description of the system, \
            including: \n \
            * The components and their interactions. \
            * The desired behaviors of the system. \
            * Any constraints, safety, or performance requirements.\n"

    prompt += "Output: \n \
        * A list of simple invariants expressed in mathematical notation where \
            each invariant is mapped to a portion of the task."

    prompt += task

    specs = chat_constrained(prompt, Model.gpt35, invariantList)
    list_of_inv = "\n".join(
        [f"[Invariant {i+1}] " + s.invariant for i, s in enumerate(specs.inv_list)]
    )

    new_task = task
    new_task += "\n Make sure that you satisfy the following specifications: \n"
    new_task += list_of_inv
    return new_task, list_of_inv


def get_task_with_LTL_specs(task):
    """ask an llm to come up with specs for task"""
    prompt = "You are an expert in formal methods, specializing in generating\
          system properties and specifications. Your task is to generate invariants\
              and LTL specifications for a system based on its natural language\
                  description.\n"

    prompt += "Guidelines:\n \
    1. Invariants: Identify properties that must hold true in all states of \
        the system. These are conditions that are always true regardless of\
              the system's execution path.\n \
    2. LTL Specifications: Formulate Linear Temporal Logic properties that \
        capture temporal behaviors of the system. These properties should \
            describe relationships or constraints that hold over time \
                (e.g., safety, liveness, fairness).\n"

    prompt += "Input: \n \
        I will provide you with a natural language description of the system, \
            including: \n \
            * The components and their interactions. \
            * The desired behaviors of the system. \
            * Any constraints, safety, or performance requirements.\n"

    prompt += "Output: \n \
        * A list of invariants expressed in mathematical notation \
        * A list of LTL Specifications in standard syntax (e.g., G (p -> Fq), \
            where G is 'Globally' and F is 'Eventually'). \
        * Provide explanations for each property, detailing why it is relevant \
            and representative of the system.\n"

    prompt += task

    specs = chat(prompt, Model.gpt35)

    new_task = task
    new_task += "\n Make sure that you satisfy the following specifications: \n"
    new_task += specs

    return new_task


def get_err_message_summary(model, error_message, nl_desc):
    prompt = "You are an expert formal methods engineer tasked with debugging\
          and refining a Python model. The model was generated from a natural\
              language description of a system but fails to satisfy some of the\
                  required properties. Analyze the model and the error message step\
                      by step, and ONLY suggest clear, actionable, and specific\
                          clarifications to the TASK. Focus on ensuring semantic\
                              accuracy and alignment with the original description.\n"
    # prompt += "Format your response like the following: [Hint 1] \
    # The specification block shouldn't have 'return True' because \
    # it isn't helpful for validating program execution.\n"
    prompt += f"Natural Language Description: {nl_desc}\n"
    prompt += f"Generated Python Model: {model}\n"
    prompt += f"Specification Counterexamples: {error_message}\n"
    prompt += "Please ONLY provide your suggestions for material to add to the \
        task description without providing any python code. Return the most\
              important hints first."
    summary = chat(prompt, Model.gpt4)
    return summary


def get_err_message_summary_constrained(model, error_message, nl_desc):
    class Suggestion(BaseModel):
        description: str
        related_cex: str

    class SuggestionList(BaseModel):
        suggestions: list[Suggestion]

    prompt = """You are a formal methods specialist analyzing failed verification\
          attempts. Your task is to:
1. Identify why the generated UCLID5 model failed to satisfy specifications
2. Determine what information is missing/ambiguous in the original task description
3. Propose precise natural language clarifications to prevent similar errors

Follow this analysis framework:
a) Map counterexample states to system requirements
b) Identify temporal/logical constraints violated in the error trace
c) Locate ambiguous predicates or incomplete invariants in the NL description
d) Suggest minimal, impactful task description additions

Focus exclusively on requirements-level clarifications - NEVER suggest code changes."""

    prompt += f"\n\nORIGINAL TASK DESCRIPTION:\n{nl_desc}"
    prompt += f"\n\nGENERATED UCLID5 MODEL:\n{model}"
    prompt += f"\n\nVERIFICATION FAILURE ANALYSIS:\n{error_message}"

    user_prompt = """Provide 2 hints using this format:
- <Concise imperative statement about required task clarification> \n
Example:
Explicitly specify maximum allowed latency between request and \
    response (CE shows 5-cycle delay in line 45) \n """

    summary = chat_constrained(prompt, user_prompt, SuggestionList)
    return "\n".join(
        [f"[Hint {i+1}] " + s.description for i, s in enumerate(summary.suggestions)]
    )


# do the updating logic
def process_code(code):
    # Find all define names without parameters (those without parentheses)
    define_names = set(re.findall(r"^\s*define\s+(\w+)\s*:", code, flags=re.MULTILINE))

    # Process each name to replace occurrences without parentheses
    for name in define_names:
        # Use a regex that matches the whole word not followed by \
        # '(' (with possible whitespace)
        pattern = re.compile(
            r"\b{}\b(?!\s*\()".format(re.escape(name)), flags=re.MULTILINE
        )
        code = pattern.sub(f"{name}()", code)

    return code


def get_module_name(code):
    pattern = r"module\s+([a-zA-Z0-9_]+)\s*{"
    match = re.search(pattern, code)
    module_name = ""
    if match:
        module_name = match.group(1)

    return module_name
