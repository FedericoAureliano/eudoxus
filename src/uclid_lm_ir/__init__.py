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
    task: str,
    output: Annotated[Optional[Path], typer.Option()] = None,
    samples: int = 1,
):
    """
    Write UCLID5 code for the given task. The output may contain holes (??).
    """
    for i in range(samples):
        code = sketch_api(task)
        if output:
            if samples > 1:
                output = output.parent / f"{output.stem}_{i}{output.suffix}"
            with open(output, "w") as f:
                f.write(code)
        else:
            syntax = Syntax(code, "scala", theme="monokai", line_numbers=True)
            console = Console()
            console.print(Panel(syntax, title="UCLID5 Output", expand=False))


@eudoxus.command()
def complete(
    code: Path,
    embeddings: bool = False,
    output: Annotated[Optional[Path], typer.Option()] = None,
    samples: int = 1,
):
    """
    Take a UCLID5 model with holes (??) and complete it using the language model.
    """
    with open(code, "r") as f:
        code_with_holes = f.read()

    for i in range(samples):
        code = complete_api(code_with_holes)
        if output:
            if samples > 1:
                output = output.parent / f"{output.stem}_{i}{output.suffix}"
            with open(output, "w") as f:
                f.write(code)
        else:
            syntax = Syntax(code, "scala", theme="monokai", line_numbers=True)
            console = Console()
            console.print(Panel(syntax, title="UCLID5 Output", expand=False))
