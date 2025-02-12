import sys
import time
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
from eudoxus.utils import generator_log, llm_log


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


@eudoxus.command()
def main_(
    task: Path,
    language: Language = Language.uclid,
    model: Model = Model.gpt35,
    output: Path = None,
    iterations: int = 2,
    inference: bool = True,
    remind: bool = True,
    solver: Annotated[bool, typer.Option(hidden=True)] = True,
    debug: Annotated[bool, typer.Option(hidden=True)] = False,
    semantic_assistance: SemanticInvolvement = SemanticInvolvement.vanilla
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

    pipeline(
        task, language, model, output, inference, iterations, debug, remind, solver, semantic_assistance
    )

    if output is not sys.stdout:
        output.close()


def pipeline(
    task, language, model, output, inference, iterations, debug, remind, solver, semantic_assistance
):
    clocks = {"llm": 0, "repair": 0}

    def timeit(clock, f, *args, **kwargs):
        time1 = time.time()
        ret = f(*args, **kwargs)
        time2 = time.time()
        clocks[clock] += time2 - time1
        return ret

    with open(task, "r") as f:
        task = f.read()

    if iterations < 1:
        # assume task is a path to a file with code to repair
        repair(task, language, output, inference, debug, solver)
        return

    if semantic_assistance == SemanticInvolvement.external_llm:
        task = get_task_with_specs(task)
    prompt = get_sketch_prompt(task, semantic_assistance)
    generator_log("Prompt:", prompt)
    llm_response = timeit("llm", chat, prompt, model)
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

    llm_calls = 1
    for _ in range(1, iterations):
        if "??" not in repaired:
            break
        prompt = get_complete_prompt(repaired, task, remind)
        generator_log("Prompt:", prompt)
        llm_response = timeit("llm", chat, prompt, model)
        llm_log("Response:", llm_response)
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

    stats = f"Original Lines: {len(original.splitlines())}\n"
    stats += f"Final Lines:    {len(repaired.splitlines())}\n"
    stats += f"LLM Calls:      {llm_calls}\n"
    stats += f"LLM Time:       {clocks['llm']:.2f}s\n"
    stats += f"Repair Time:    {clocks['repair']:.2f}s"
    generator_log("Stats:", stats)

    repair(repaired, language, output, False, debug, solver)


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
        src = src.encode()

    modules = Parser(src, debug).parse()
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

    write()


def get_task_with_specs(task):
    """ ask an llm to come up with specs for task """
    prompt = "You are an expert in formal methods, specializing in generating system properties and specifications. Your task is to generate invariants and LTL specifications for a system based on its natural language description.\n"

    prompt += "Guidelines:\n \
    1. Invariants: Identify properties that must hold true in all states of the system. These are conditions that are always true regardless of the system's execution path.\n \
    2. LTL Specifications: Formulate Linear Temporal Logic properties that capture temporal behaviors of the system. These properties should describe relationships or constraints that hold over time (e.g., safety, liveness, fairness).\n"

    prompt += "Input: \n \
        I will provide you with a natural language description of the system, including: \n \
            * The components and their interactions. \
            * The desired behaviors of the system. \
            * Any constraints, safety, or performance requirements.\n"

    prompt += "Output: \n \
        * A list of invariants expressed in mathematical notation \
        * A list of LTL Specifications in standard syntax (e.g., G (p -> Fq), where G is 'Globally' and F is 'Eventually'). \
        * Provide explanations for each property, detailing why it is relevant and representative of the system.\n"

    prompt += task

    specs = chat(prompt, Model.gpt35)

    new_task = task
    new_task += "\n Make sure that you satisfy the following specifications: \n"
    new_task += specs
    
    return new_task