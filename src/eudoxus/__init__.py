import sys
from enum import Enum
from pathlib import Path

import typer

from eudoxus.checker.declared import DeclaredChecker
from eudoxus.checker.type import TypeChecker
from eudoxus.parser.python import Parser
from eudoxus.printer.python import module2py
from eudoxus.printer.uclid import module2ucl
from eudoxus.rewriter import Rewriter


class Language(str, Enum):
    python = "python"
    uclid = "uclid"


eudoxus = typer.Typer(pretty_exceptions_enable=False, add_completion=False)


@eudoxus.command()
def main_(
    src: Path,
    language: Language = Language.python,
    output: Path = None,
    check: bool = True,
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

    main(src, language, output, check)

    if output is not sys.stdout:
        output.close()


def main(src, language, output, check):
    def write():
        if language == Language.python:
            for m in modules:
                module2py(output, m, 0)

        if language == Language.uclid:
            for m in modules:
                module2ucl(output, m, 0)

    with open(src, "rb") as f:
        src = f.read()

    modules = Parser(src).parse()

    if check:
        checkers = [DeclaredChecker, TypeChecker]
    else:
        checkers = []

    for checker in checkers:
        rewrites = checker().check(modules)
        rewriter = Rewriter(rewrites)
        modules = [rewriter.rewrite(m) for m in modules]

    write()
