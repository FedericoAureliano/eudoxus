from importlib.metadata import PackageNotFoundError, version  # pragma: no cover
from pathlib import Path
from typing import Optional

import typer
from rich.console import Console
from rich.panel import Panel
from rich.syntax import Syntax
from typing_extensions import Annotated

try:
    # Change here if project is renamed and does not equal the package name
    dist_name = "eudoxus"
    __version__ = version(dist_name)
except PackageNotFoundError:  # pragma: no cover
    __version__ = "unknown"
finally:
    del version, PackageNotFoundError

from .generate import complete_api, process_code, sketch_api
from .module import Module

__all__ = [
    "Module",
    "sketch_api",
    "complete_api",
]

eudoxus = typer.Typer(
    add_completion=False,
    no_args_is_help=True,
    help="UCLID5 code generation using language models.",
)


@eudoxus.command()
def synthesize(
    task: Annotated[
        Optional[str],
        typer.Argument(
            help="Description of the desired UCLID5 code in natural language"
        ),
    ],
    examples: Annotated[
        Optional[Path],
        typer.Option(help="Directory with example UCLID5 files to use for RAG"),
    ] = None,
    neighbours: Annotated[
        int, typer.Option(help="Number of neighbours to consider for RAG")
    ] = 1,
    save_ir: Annotated[Path, typer.Option(help="Save the IR to a file")] = None,
    output: Annotated[Optional[Path], typer.Option(help="File to write to")] = None,
    remind: Annotated[
        bool,
        typer.Option(help="Remind the LLM of the task description during completion"),
    ] = False,
) -> None:
    """
    Synthesize a complete UCLID5 model from a natural language description.
    """
    code_with_holes = sketch_api(task, save_ir=save_ir)
    task = task if remind else None
    code = complete_api(code_with_holes, examples, neighbours, task)
    syntax = Syntax(code, "scala", theme="monokai", line_numbers=True)
    console = Console()
    console.print(Panel(syntax, title="UCLID5 Output", expand=False))
    if output:
        with open(output, "w") as f:
            f.write(code)


@eudoxus.command()
def sketch(
    task: Annotated[
        str,
        typer.Argument(
            help="Description of the desired UCLID5 code in natural language"
        ),
    ],
    output: Annotated[Optional[Path], typer.Option(help="File to write to")] = None,
    samples: Annotated[int, typer.Option(help="Number of times to query the LLM")] = 1,
    save_ir: Annotated[Path, typer.Option(help="Save the IR to a file")] = None,
):
    """
    Write UCLID5 code for the given task. The output may contain holes (??).
    """
    for i in range(samples):
        if save_ir and samples > 1:
            save_ir_i = save_ir.parent / f"{save_ir.stem}_{i}{save_ir.suffix}"
        else:
            save_ir_i = save_ir

        if output and samples > 1:
            output_i = output.parent / f"{output.stem}_{i}{output.suffix}"
        else:
            output_i = output

        code = sketch_api(task, save_ir=save_ir_i)

        if output:
            with open(output_i, "w") as f:
                f.write(code)
        else:
            syntax = Syntax(code, "scala", theme="monokai", line_numbers=True)
            console = Console()
            console.print(Panel(syntax, title="UCLID5 Output", expand=False))


@eudoxus.command()
def fill(
    code: Annotated[Path, typer.Argument(help="Path to input file with UCLID5 code")],
    output: Annotated[Optional[Path], typer.Option(help="File to write to")] = None,
    samples: Annotated[int, typer.Option(help="Number of times to query the LLM")] = 1,
    examples: Annotated[
        Optional[Path],
        typer.Option(help="Directory with example UCLID5 files to use for RAG"),
    ] = None,
    neighbours: Annotated[
        int, typer.Option(help="Number of neighbours to consider for RAG")
    ] = 1,
):
    """
    Take a UCLID5 model with holes (??) and complete it using a language model.
    """
    with open(code, "r") as f:
        code_with_holes = f.read()

    for i in range(samples):
        code = complete_api(code_with_holes, examples, neighbours)
        if output:
            if samples > 1:
                output_i = output.parent / f"{output.stem}_{i}{output.suffix}"
            else:
                output_i = output
            with open(output_i, "w") as f:
                f.write(code)
        else:
            syntax = Syntax(code, "scala", theme="monokai", line_numbers=True)
            console = Console()
            console.print(Panel(syntax, title="UCLID5 Output", expand=False))


@eudoxus.command(hidden=True)
def add_to_tests(
    python_file: Annotated[Path, typer.Argument(help="Path to file with Python IR")],
    uclid_file: Annotated[
        Path, typer.Argument(help="Path file with desired UCLID5 output")
    ],
    name: Annotated[str, typer.Argument(help="Name of the test")],
    tests_file: Annotated[
        Path, typer.Option(help="Path to regression tests file")
    ] = "tests/test_regressions.py",
):
    """
    Add a new regression test to the test suite.
    """
    with open(python_file, "r") as f:
        python_ir = f.read()
    with open(uclid_file, "r") as f:
        uclid_ir = f.read()

    with open(tests_file, "a") as f:
        f.write(
            f"""\n
def test_{name}():
    code = \"""{python_ir}\"""
    expected = \"""{uclid_ir}\"""
    python = ast.parse(code)
    output = compile_to_uclid5(python)
    assert_equal(output, expected)
"""
        )
    console = Console()
    console.print(
        Panel(
            f"Added test_{name} to tests/test_regression.py",
            title="Success",
            expand=False,
        )
    )


@eudoxus.command()
def process_python(
    python_file: Annotated[Path, typer.Argument(help="Path to file with Python IR")],
    output: Annotated[Optional[Path], typer.Option(help="File to write to")] = None,
):
    """
    Process a Python IR file and write the result to a new file.
    """
    with open(python_file, "r") as f:
        python_ir = f.read()

    code = process_code(python_ir)

    if output:
        with open(output, "w") as f:
            f.write(code)
    else:
        syntax = Syntax(code, "scala", theme="monokai", line_numbers=True)
        console = Console()
        console.print(Panel(syntax, title="UCLID5 Output", expand=False))
