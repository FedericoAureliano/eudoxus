from importlib.metadata import PackageNotFoundError, version  # pragma: no cover

try:
    # Change here if project is renamed and does not equal the package name
    dist_name = "uclid_lm_ir"
    __version__ = version(dist_name)
except PackageNotFoundError:  # pragma: no cover
    __version__ = "unknown"
finally:
    del version, PackageNotFoundError

from .control import induction
from .generate import get_prompt, gpt4_write_code
from .module import Module
from .printer import print_uclid5
from .types import BitVector, Integer

__all__ = [
    "Module",
    "Integer",
    "BitVector",
    "induction",
    "print_uclid5",
    "get_prompt",
    "gpt4_write_code",
]
