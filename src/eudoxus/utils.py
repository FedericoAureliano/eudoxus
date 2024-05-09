import functools

from rich.console import Console
from rich.panel import Panel

console = Console()
GENERATOR_STYLE = "blue"
LLM_STYLE = "bold magenta"


def foldl(func, acc, xs):
    return functools.reduce(func, xs, acc)


def generator_log(*messages):
    """Logs a message from the generator."""

    if len(messages) > 1:
        message = " ".join([str(m) for m in messages[1:]])
        message = Panel(message, title=":robot: " + messages[0], expand=False)
    else:
        message = ":robot: " + messages[0]

    console.log(
        message,
        style=GENERATOR_STYLE,
        markup=True,
        emoji=True,
        justify="full",
        highlight=False,
    )


def llm_log(*messages):
    """Logs a message from the llm."""
    if len(messages) > 1:
        message = " ".join([str(m) for m in messages[1:]])
        message = Panel(message, title=":brain: " + messages[0], expand=False)
    else:
        message = ":brain: " + messages[0]

    console.log(
        message,
        style=LLM_STYLE,
        markup=True,
        emoji=True,
        justify="full",
        highlight=False,
    )
