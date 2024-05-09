import sys
from enum import Enum
from io import StringIO
from pathlib import Path

import typer

from eudoxus.checker.declared import DeclaredChecker
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
    language: Language = Language.python,
    output: Path = None,
    inference: bool = True,
    max_llm_calls: int = 2,
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

    pipeline(task, language, output, inference, max_llm_calls)

    if output is not sys.stdout:
        output.close()


def pipeline(task, language, output, inference, max_llm_calls):
    with open(task, "r") as f:
        task = f.read()

    prompt = get_sketch_prompt(task)
    generator_log("Prompt:", prompt)
    llm_response = chat(prompt)
    llm_log("Response:", llm_response)
    python = extract_code(llm_response)
    generator_log("Extracted:", python)
    repaired = StringIO()
    repair(python, Language.python, repaired, inference)
    repaired = repaired.getvalue()
    generator_log("Repaired:", repaired)

    for _ in range(1, max_llm_calls):
        if "??" not in repaired:
            break
        prompt = get_complete_prompt(repaired)
        generator_log("Prompt:", prompt)
        llm_response = chat(prompt)
        llm_log("Response:", llm_response)
        python = extract_code(llm_response)
        generator_log("Extracted:", python)
        repaired = StringIO()
        repair(python, Language.python, repaired, inference)
        repaired = repaired.getvalue()
        generator_log("Repaired:", repaired)

    repair(repaired, language, output, inference)


def repair(src, language, output, inference):
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
        checkers = [DeclaredChecker, TypeChecker]
    else:
        checkers = []

    for checker in checkers:
        rewrites = checker().check(modules)
        rewriter = Rewriter(rewrites)
        modules = [rewriter.rewrite(m) for m in modules]

    write()
