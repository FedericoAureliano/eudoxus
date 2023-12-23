import ast
from enum import Enum


class Kind(Enum):
    """The kind of log message."""

    USER = 1
    LLM = 2
    GENERATOR = 3
    WARNING = 4


class bcs:
    HEADER = "\033[95m"
    BLUE = "\033[94m"
    CYAN = "\033[96m"
    GREEN = "\033[92m"
    WARNING = "\033[93m"
    FAIL = "\033[91m"
    END = "\033[0m"
    BF = "\033[1m"
    UL = "\033[4m"


def log(text, kind: Kind, note=""):
    if note:
        note = f" ({note})"
    match kind:
        case Kind.USER:
            print(f"{bcs.BF}**** User{bcs.END}{note}:\n{bcs.BLUE}{text}{bcs.END}\n\n")
        case Kind.LLM:
            print(f"{bcs.BF}**** LLM{bcs.END}{note}:\n{bcs.GREEN}{text}{bcs.END}\n\n")
        case Kind.GENERATOR:
            print(
                f"{bcs.BF}**** Generator{bcs.END}{note}:\n{bcs.CYAN}{text}{bcs.END}\n\n"
            )
        case Kind.WARNING:
            print(f"{bcs.BF}Warning{bcs.END}{note}: {bcs.WARNING}{text}{bcs.END}\n")


def dump(node):
    return ast.dump(node, indent=2)


def infer_type(value: str) -> str:
    """Infers the type of a string value."""
    if value in ["integer", "boolean"]:
        return value
    elif value.startswith("bv"):
        return value
    elif value.isdigit():
        return "Integer"
    elif value == "True" or value == "False":
        return "Boolean"
    else:
        log(f"Could not infer type of {value}, leaving as is.", Kind.WARNING)
        return value
