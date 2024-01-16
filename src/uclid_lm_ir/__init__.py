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
    dist_name = "uclid_lm_ir"
    __version__ = version(dist_name)
except PackageNotFoundError:  # pragma: no cover
    __version__ = "unknown"
finally:
    del version, PackageNotFoundError

from .generate import complete_api, sketch_api
from .module import Module

__all__ = [
    "Module",
    "sketch_api",
    "complete_api",
]

eudoxus = typer.Typer()


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
):
    """
    Write UCLID5 code for the given task. The output may contain holes (??).
    """
    for i in range(samples):
        code = sketch_api(task)
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


@eudoxus.command()
def complete(
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
