import csv
import sys
import time
from datetime import datetime
from enum import Enum
from io import StringIO
from pathlib import Path

import typer
from typing_extensions import Annotated

from eudoxus.emit.python import module2py
from eudoxus.emit.uclid import module2ucl
from eudoxus.llm.gpt import chat
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
from eudoxus.utils import (
    add_control_block,
    change_model,
    filter_cex,
    generator_log,
    get_bmc_error_fixes,
    get_smoke_error_fixes,
    insert_block_fixes,
    llm_log,
    rewrite_module_with_llm_bmc,
    run_smoke_testing,
    run_uclid,
    uclid_log,
)


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
    semantic_assistance: bool = False,
    use_bmc: bool = False,
    use_smoke: bool = False,
    csv_loc: str = "",
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
    # if iterations < 1:
    if not semantic_assistance and not (use_bmc or use_smoke):
        repaired, _, _ = syntax_pipeline(
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
        )
        repair(repaired, language, output, False, debug, solver)
        if output is not sys.stdout:
            output.close()
    else:
        # initialize the csv
        if csv_loc:
            with open(csv_loc, "w", newline="") as file:
                writer = csv.writer(file)
                writer.writerow(
                    [
                        "task",
                        "date",
                        "use_bmc",
                        "use_smoke",
                        "force external spec",
                        "passed_assertions",
                        "failed_assertions",
                        "original_lines",
                        "final_lines",
                        "llm_calls",
                        "llm_time",
                        "repair_time",
                        "Spec Defined",
                        "Exit Cause",
                        "output_name",
                        "smoke warnings",
                        "sem loop time",
                        "num. suggested fixes",
                        "total tokens",
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
            use_bmc,
            use_smoke,
            csv_loc,
            sem_iters,
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
    gen_ext_spec,
    use_bmc,
    use_smoke,
    csv_loc,
    sem_iters,
):
    MAX_SEM_ITER = sem_iters
    sem_iter = 0
    UCL_LOC = "testing_numbers.ucl"
    BASE_TASK_LOC = task
    date = datetime.now()

    all_stats = []
    code_with_fix_holes = ""  # starts off as empty
    best_model_info = {}
    best_model_info["model"] = ""
    best_model_info["passed_assertions"] = 0
    best_model_info["failed_assertions"] = 0
    best_model_info["uclid_passes"] = False
    best_model_info["warnings"] = 0
    while True:
        if sem_iter == MAX_SEM_ITER:
            break
        start_time = time.time()
        sem_iter += 1
        uclid_passes = False
        spec_defined = False
        failed_assertions = 0
        passed_assertions = 0
        warnings = 54321
        block_fix_pair_list = []
        # TODO: Perhaps only need to do this if we have verf feedback... but not sure
        semantic_stats = f"  SEMANTIC ITERATION {sem_iter}\n"
        task = BASE_TASK_LOC
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
            gen_ext_spec,
            code_with_fix_holes,
        )
        original_lines = stat_dict["original_lines"]
        final_lines = stat_dict["final_lines"]
        llm_calls = stat_dict["llm_calls"]
        llm_time = stat_dict["llm_time"]
        repair_time = stat_dict["repair_time"]
        spec_defined = "def specification(self)" in syntatic_correct_py_code
        stats = semantic_stats + stats
        if not (use_bmc or use_smoke):
            if csv_loc:
                with open(csv_loc, "a+") as file:
                    writer = csv.writer(file)
                    passed_assertions = ""
                    failed_assertions = ""
                    smoke_warnings = ""
                    sem_loop_time = round(time.time() - start_time, 2)
                    num_suggested_fixes = ""
                    total_tokens = ""
                    writer.writerow(
                        [
                            BASE_TASK_LOC,
                            date,
                            use_bmc,
                            use_smoke,
                            gen_ext_spec,
                            passed_assertions,
                            failed_assertions,
                            original_lines,
                            final_lines,
                            llm_calls,
                            llm_time,
                            repair_time,
                            spec_defined,
                            "user did not want verification",
                            output.name,
                            smoke_warnings,
                            sem_loop_time,
                            num_suggested_fixes,
                            total_tokens,
                        ]
                    )
            best_model_info["model"] = syntatic_correct_py_code
            break

        UCL_out_fd = open(UCL_LOC, "w")
        encoded_py_code = syntatic_correct_py_code.encode()
        modules = Parser(encoded_py_code).parse()

        modules = [m for m in modules if not m.is_empty()]
        python_out_fd = open("testing_numbers.py", "w")
        for m in modules:
            module2ucl(UCL_out_fd, m, 0)
            module2py(python_out_fd, m, 0)
        UCL_out_fd.close()
        python_out_fd.close()

        # bring back the files with the statement ids
        read_fd = open(UCL_LOC, "r")
        module_as_ucl = read_fd.read()
        read_fd.close()

        new_python_fd = open("testing_numbers.py", "r")
        syntatic_correct_py_code = new_python_fd.read()
        new_python_fd.close()

        if "??" in module_as_ucl:
            print("found ?? in model, can't run uclid")
            stats += "Failed Assertions: N/A\n"
            stats += "Passed Assertions: N/A\n"
            stats += "-------------------\n"
            all_stats.append(stats)
            if csv_loc:
                with open(csv_loc, "a+") as file:
                    writer = csv.writer(file)
                    smoke_warnings = ""
                    sem_loop_time = round(time.time() - start_time, 2)
                    num_suggested_fixes = ""
                    total_tokens = ""
                    writer.writerow(
                        [
                            BASE_TASK_LOC,
                            date,
                            use_bmc,
                            use_smoke,
                            gen_ext_spec,
                            passed_assertions,
                            failed_assertions,
                            original_lines,
                            final_lines,
                            llm_calls,
                            llm_time,
                            repair_time,
                            spec_defined,
                            "holes in the uclid module",
                            output.name,
                            smoke_warnings,
                            sem_loop_time,
                            num_suggested_fixes,
                            total_tokens,
                        ]
                    )
            continue

        # RUN UCLID
        if use_bmc:
            uclid_log("UCL MOD BEFORE BMC", module_as_ucl)
            passed_assertions, failed_assertions, stdout, uclid_passes = run_uclid(
                module_as_ucl, task, syntatic_correct_py_code, iterations=0
            )
            print(
                f"ran uclid with 0 iterations | \
                    passed: {passed_assertions} |\
                          failed: {failed_assertions}"
            )

            if (
                failed_assertions == 0
                and passed_assertions != 0
                and "errors found." not in stdout
            ):
                passed_assertions, failed_assertions, stdout, uclid_passes = run_uclid(
                    module_as_ucl, task, syntatic_correct_py_code, iterations=3
                )
                print(
                    f"ran uclid with 3 iterations | \
                        passed: {passed_assertions} |\
                              failed: {failed_assertions}"
                )

                if (
                    failed_assertions == 0
                    and passed_assertions != 0
                    and "errors found." not in stdout
                ):
                    (
                        passed_assertions,
                        failed_assertions,
                        stdout,
                        uclid_passes,
                    ) = run_uclid(
                        module_as_ucl, task, syntatic_correct_py_code, llm_call=True
                    )
                    print(
                        f"ran uclid with llm iterations | \
                            passed: {passed_assertions} | \
                                failed: {failed_assertions}"
                    )

            stats += f"Failed Assertions:  {failed_assertions}\n"
            stats += f"Passed Assertions:  {passed_assertions}\n"

            uclid_log("Original UCLID Terminal Output: ", stdout)
            # FILTER OUTPUT
            if uclid_passes:
                if not spec_defined:
                    final_uclid_cex = "No specification block defined. Make sure \
                        the specifications represent the essence of the\
                              task description.\n"
                    uclid_passes = False

            uclid_cex = stdout.lower()
            final_uclid_cex = filter_cex(uclid_cex)
            if not final_uclid_cex and uclid_passes:  # empty uclid cex and uclid pass
                final_uclid_cex = "All BMC cases passed"
            if "errors found" in final_uclid_cex:
                uclid_passes = False

            uclid_log(
                "Filtered UCLID Terminal Output: ", final_uclid_cex, style="green"
            )

            if (
                not use_smoke
                and failed_assertions == 0
                and uclid_passes
                and passed_assertions != 0
            ):
                print(
                    "stopping condition for just using bmc (found no \
                        failed assertions and uclid passes)"
                )
                best_model_info["model"] = syntatic_correct_py_code
                stats += "-------------------\n"
                all_stats.append(stats)
                if csv_loc:
                    with open(csv_loc, "a+") as file:
                        writer = csv.writer(file)
                        smoke_warnings = ""
                        sem_loop_time = round(time.time() - start_time, 2)
                        num_suggested_fixes = ""
                        total_tokens = ""
                        writer.writerow(
                            [
                                BASE_TASK_LOC,
                                date,
                                use_bmc,
                                use_smoke,
                                gen_ext_spec,
                                passed_assertions,
                                failed_assertions,
                                original_lines,
                                final_lines,
                                llm_calls,
                                llm_time,
                                repair_time,
                                spec_defined,
                                "uclid passed and no failed assertions",
                                output.name,
                                smoke_warnings,
                                sem_loop_time,
                                num_suggested_fixes,
                                total_tokens,
                            ]
                        )
                break

            with open(BASE_TASK_LOC, "r") as f:
                task_ = f.read()
            if failed_assertions != 0:
                block_fix_pair_list = get_bmc_error_fixes(
                    syntatic_correct_py_code, final_uclid_cex, task_
                )

        # SMOKE TESTING
        if use_smoke:
            if use_bmc and failed_assertions != 0:
                print("smoke feature enabled, but failed bmc so not running")
            else:
                with open(BASE_TASK_LOC, "r") as f:
                    task_ = f.read()
                module_as_ucl = add_control_block(module_as_ucl)
                module_as_ucl = rewrite_module_with_llm_bmc(
                    task_, syntatic_correct_py_code, module_as_ucl
                )
                uclid_log("UCL MOD BEFORE SMOKE TESTING", module_as_ucl)
                warnings, final_uclid_cex = run_smoke_testing(module_as_ucl)
                if not use_bmc or (use_bmc and failed_assertions == 0):
                    block_fix_pair_list = get_smoke_error_fixes(
                        syntatic_correct_py_code, final_uclid_cex, task_
                    )
                stats += f"Warnings:        {warnings}\n"
                if (warnings == 0 and not use_bmc) or (
                    warnings == 0 and use_bmc and passed_assertions != 0
                ):
                    best_model_info["model"] = syntatic_correct_py_code
                    stats += "-------------------\n"
                    all_stats.append(stats)
                    if csv_loc:
                        with open(csv_loc, "a+") as file:
                            writer = csv.writer(file)
                            sem_loop_time = round(time.time() - start_time, 2)
                            num_suggested_fixes = ""
                            total_tokens = ""
                            writer.writerow(
                                [
                                    BASE_TASK_LOC,
                                    date,
                                    use_bmc,
                                    use_smoke,
                                    gen_ext_spec,
                                    passed_assertions,
                                    failed_assertions,
                                    original_lines,
                                    final_lines,
                                    llm_calls,
                                    llm_time,
                                    repair_time,
                                    spec_defined,
                                    "smoke testing found no warnings",
                                    output.name,
                                    warnings,
                                    sem_loop_time,
                                    num_suggested_fixes,
                                    total_tokens,
                                ]
                            )
                    break

        stats += "-------------------\n"
        all_stats.append(stats)

        # COMPARE MODELS

        if change_model(
            passed_assertions,
            failed_assertions,
            uclid_passes,
            warnings,
            best_model_info,
            use_bmc,
            use_smoke,
        ):
            print("changed model")
            best_model_info["model"] = syntatic_correct_py_code
            best_model_info["passed_assertions"] = passed_assertions
            best_model_info["failed_assertions"] = failed_assertions
            best_model_info["uclid_passes"] = uclid_passes
            best_model_info["warnings"] = warnings

        llm_log("SYNTACTIC CORRECT CODE: ", syntatic_correct_py_code)
        uclid_log("UCLID CEX: ", final_uclid_cex)

        # if verf_eng_feedback:
        #     if uclid_passes:
        #         print("uclid passed: ", uclid_passes)
        #         if warnings == 0:
        #             print("smoke testing did not find unreachable lines")
        #             uclid_log("BEST UCLID: ", module_as_ucl, style="green")
        #             break

        # get the base task from the location
        with open(BASE_TASK_LOC, "r") as f:
            task = f.read()

        block_fix_pair_string = ""
        for b, f in block_fix_pair_list:
            block_fix_pair_string += f"block: {b}\n"
            block_fix_pair_string += f"fix: {f}\n\n"
        llm_log("Summarized (Constrained) Error Message", block_fix_pair_string)

        for block, fix in block_fix_pair_list:
            # todo, have a check for ablock that doesn't exist or isn't allowed
            block = block.lower()
            if "init" in block:
                syntatic_correct_py_code = insert_block_fixes(
                    "def init(self):", syntatic_correct_py_code, fix
                )

            elif "locals" in block:
                syntatic_correct_py_code = insert_block_fixes(
                    "def locals(self):", syntatic_correct_py_code, fix
                )

            elif "next" in block:
                syntatic_correct_py_code = insert_block_fixes(
                    "def next(self):", syntatic_correct_py_code, fix
                )

            elif "specification" in block:
                syntatic_correct_py_code = insert_block_fixes(
                    "def specification(self):", syntatic_correct_py_code, fix
                )

        code_with_fix_holes = syntatic_correct_py_code

        llm_log("LLM SPEC LOOP RESPONSE: ", code_with_fix_holes)

        if csv_loc:
            with open(csv_loc, "a+") as file:
                writer = csv.writer(file)
                sem_loop_time = round(time.time() - start_time, 2)
                num_suggested_fixes = len(block_fix_pair_list)
                total_tokens = ""
                writer.writerow(
                    [
                        BASE_TASK_LOC,
                        date,
                        use_bmc,
                        use_smoke,
                        gen_ext_spec,
                        passed_assertions,
                        failed_assertions,
                        original_lines,
                        final_lines,
                        llm_calls,
                        llm_time,
                        repair_time,
                        spec_defined,
                        f"finished iteration {sem_iter}",
                        output.name,
                        warnings,
                        sem_loop_time,
                        num_suggested_fixes,
                        total_tokens,
                    ]
                )

    generator_log("Stats:", " ".join(all_stats))
    best_py_model = best_model_info["model"]
    repair(best_py_model, language, output, False, debug, solver)

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

    # hopefully you don't need this but in case, this is still kind of here
    # for insert_loc in open_locations:
    #     code = insert_string(code)

    if stack:
        for _ in stack:
            code += ")"

    return code


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
    gen_ext_spec,
    code_with_holes="",
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

    # if (not code_with_holes and not gen_ext_spec):
    prompt = get_sketch_prompt(task, spec_format="default")

    if gen_ext_spec:
        if code_with_holes:
            prompt = get_complete_prompt(
                code_with_holes, task, remind, spec_format="force_spec"
            )
        else:
            prompt = get_sketch_prompt(task, spec_format="specless")

    llm_response = timeit("llm", chat, prompt, model)

    generator_log("Prompt:", prompt)
    llm_log("Response:", llm_response)
    python = extract_code(llm_response)
    original = python
    generator_log("Extracted:", python)
    repaired = StringIO()
    timeit(
        "repair", repair, python, Language.python, repaired, inference, debug, solver
    )
    repaired = repaired.getvalue()
    generator_log("Repaired:", repaired)
    revert_to = repaired

    llm_calls = 1
    for _ in range(1, iterations):
        if len(repaired) < 10:  # in case repaired is really messed up
            print("repaired is messed up")
            repaired = revert_to
        else:
            revert_to = repaired

        # if we are not running semantic then this will pass if no ??
        # if we are running semantic then this will pass if we have gone
        # through atleast once
        # want to go through atleast once in semantic bc the spec block
        # is added in the prompt below
        if "??" not in repaired and (not gen_ext_spec or llm_calls > 1):
            break

        if gen_ext_spec:
            prompt = get_complete_prompt(
                repaired, task, remind, spec_format="force_spec"
            )
        else:
            prompt = get_complete_prompt(repaired, task, remind, spec_format="default")
        generator_log("Prompt:", prompt)

        llm_response = timeit("llm", chat, prompt, model)
        llm_log("Original Response:", llm_response)

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

    original_lines = len(original.splitlines())
    final_lines = len(repaired.splitlines())
    llm_time = round(clocks["llm"], 2)
    repair_time = round(clocks["repair"], 2)

    stats = f"Original Lines: {original_lines}\n"
    stats += f"Final Lines:    {final_lines}\n"
    stats += f"LLM Calls:      {llm_calls}\n"
    stats += f"LLM Time:       {llm_time}s\n"
    stats += f"Repair Time:    {repair_time}s\n"
    generator_log("Stats:", stats)

    stats_as_dict = {
        "original_lines": original_lines,
        "final_lines": final_lines,
        "llm_calls": llm_calls,
        "llm_time": llm_time,
        "repair_time": repair_time,
    }

    return repaired, stats, stats_as_dict


def repair(src, language, output, inference, debug, solver):
    def write():
        if language == Language.python:
            for m in modules:
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
        #     print("init when printing: ", m.locals)

    write()
