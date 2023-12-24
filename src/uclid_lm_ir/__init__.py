import argparse
from importlib.metadata import PackageNotFoundError, version  # pragma: no cover

try:
    # Change here if project is renamed and does not equal the package name
    dist_name = "uclid_lm_ir"
    __version__ = version(dist_name)
except PackageNotFoundError:  # pragma: no cover
    __version__ = "unknown"
finally:
    del version, PackageNotFoundError

from .generate import gpt4_write_code
from .module import Module

__all__ = [
    "Module",
    "gpt4_write_code",
]


def eudoxus():
    parser = argparse.ArgumentParser()
    parser.add_argument("--task", help="task name", required=True)
    parser.add_argument("--output", help="output file name", required=False)
    args = parser.parse_args()

    task = args.task
    output = args.output

    code = gpt4_write_code(task)
    if output:
        with open(output, "w") as f:
            f.write(code)
