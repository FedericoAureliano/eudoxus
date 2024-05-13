import sys
import time
from enum import Enum
from io import StringIO
from pathlib import Path

import typer
from typing_extensions import Annotated

from eudoxus.checker.declared import DeclaredChecker
from eudoxus.checker.select import SelectChecker
from eudoxus.checker.type import TypeChecker
from eudoxus.llm.gpt import chat
from eudoxus.llm.prompts import get_complete_prompt, get_sketch_prompt
from eudoxus.llm.utils import extract_code
from eudoxus.parser.python import Parser
from eudoxus.printer.python import module2py
from eudoxus.printer.uclid import module2ucl
from eudoxus.rewriter import Rewriter
from eudoxus.utils import generator_log, llm_log


class Language(str, Enum):
    python = "python"
    uclid = "uclid"


eudoxus = typer.Typer(pretty_exceptions_enable=False, add_completion=False)


@eudoxus.command()
def main_(
    task: Path,
    language: Language = Language.uclid,
    output: Path = None,
    inference: bool = True,
    iterations: int = 2,
    debug: Annotated[bool, typer.Option(hidden=True)] = False,
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

    pipeline(task, language, output, inference, iterations, debug)

    if output is not sys.stdout:
        output.close()


def pipeline(task, language, output, inference, iterations, debug):
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
        repair(task, language, output, inference, debug)
        return

    prompt = get_sketch_prompt(task)
    generator_log("Prompt:", prompt)
    llm_response = timeit("llm", chat, prompt)
    llm_log("Response:", llm_response)
    python = extract_code(llm_response)
    original = python
    generator_log("Extracted:", python)
    repaired = StringIO()
    timeit("repair", repair, python, Language.python, repaired, inference, debug)
    repaired = repaired.getvalue()
    generator_log("Repaired:", repaired)

    for i in range(1, iterations):
        if "??" not in repaired:
            break
        prompt = get_complete_prompt(repaired)
        generator_log("Prompt:", prompt)
        llm_response = timeit("llm", chat, prompt)
        llm_log("Response:", llm_response)
        python = extract_code(llm_response)
        generator_log("Extracted:", python)
        repaired = StringIO()
        timeit("repair", repair, python, Language.python, repaired, inference, debug)
        repaired = repaired.getvalue()
        generator_log("Repaired:", repaired)

    stats = f"iters: {i}\n"
    stats += f"change: {len(repaired.splitlines()) - len(original.splitlines())}\n"
    stats += f"llm: {clocks['llm']:.2f}s\n"
    stats += f"repair: {clocks['repair']:.2f}s"
    generator_log("Stats:", stats)

    repair(repaired, language, output, inference, debug)


def repair(src, language, output, inference, debug):
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

    modules = Parser(src).parse()

    if inference:
        checkers = [SelectChecker, DeclaredChecker, TypeChecker]
    else:
        checkers = []

    for checker in checkers:
        rewrites = checker().check(modules)
        rewriter = Rewriter(rewrites)
        modules = [rewriter.rewrite(m) for m in modules]

    write()
