import sys
from enum import Enum
from pathlib import Path

import typer

from eudoxus.checker.type import TypeChecker
from eudoxus.dfy.checker.dafny_checker import DfyTypeChecker
from eudoxus.dfy.parser.python import DfyParser
from eudoxus.dfy.printer.dafny import module2dfy
from eudoxus.dfy.rewriter.dfy_rewriter import DfyRewriter
from eudoxus.parser.python import Parser
from eudoxus.printer.python import module2py
from eudoxus.printer.uclid import module2ucl
from eudoxus.rewriter import Rewriter


class Language(str, Enum):
    python = "python"
    uclid = "uclid"
    dafny = "dafny"


eudoxus = typer.Typer(pretty_exceptions_enable=False, add_completion=False)


@eudoxus.command()
def main_(
    src: Path,
    language: Language = Language.python,
    output: Path = None,
    check: bool = True,
    src_dsl: Language = Language.python,
) -> None:
    """
    language is the target language
    src_dsl is the dsl within python :: bit of an overload
    """
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
        if extension == ".dfy" and language != Language.dafny:
            print("Language and output file extension do not match!")
            return
        output = open(output, "w")

    main(src, language, output, check, src_dsl)

    if output is not sys.stdout:
        output.close()


def main(src, language, output, check, src_dsl):
    with open(src, "rb") as f:
        src = f.read()

    parser = Parser if src_dsl != Language.dafny else DfyParser
    checker = TypeChecker if src_dsl != Language.dafny else DfyTypeChecker

    modules = parser(src).parse()

    if check:
        rewrites = checker().check(modules)
    else:
        rewrites = {}

    rewriter = (
        Rewriter(rewrites) if src_dsl != Language.dafny else DfyRewriter(rewrites)
    )
    modules = [rewriter.rewrite(m) for m in modules]

    if language == Language.python:
        for m in modules:
            module2py(output, m, 0)

    if language == Language.uclid:
        for m in modules:
            module2ucl(output, m, 0)

    if language == Language.dafny:
        for m in modules:
            module2dfy(output, m, 0)
