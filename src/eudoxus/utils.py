import ast

from rich.console import Console
from rich.panel import Panel

console = Console()
GENERATOR_STYLE = "blue"
LLM_STYLE = "bold magenta"


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


def dump(node):
    return ast.dump(node, indent=2)


def assert_equal(actual: str, expected: str):
    print("Expected:\n")
    print(expected)
    print("\n\nActual:\n")
    print(actual)
    answer = actual.split() == expected.split()
    # find the first difference
    if not answer:
        actual = actual.split()
        expected = expected.split()
        for i in range(len(actual)):
            if actual[i] != expected[i]:
                print(f"First difference at index {i}:")
                print(f"Expected: {expected[i]}")
                print(f"Actual: {actual[i]}")
                break
    assert answer
