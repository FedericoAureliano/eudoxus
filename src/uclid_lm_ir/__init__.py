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
from .module import Module
from .printer import print_uclid5
from .types import integer_sort

__all__ = [
    "Module",
    "integer_sort",
    "induction",
    "print_uclid5",
]
