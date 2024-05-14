import os
import re
from difflib import Differ
from io import StringIO

from eudoxus import repair as eudoxus

EXAMPLES = "examples"

WHITESPACE = re.compile(r"\s+")


def clean(sentence):
    cleaned = re.sub(WHITESPACE, "", sentence)
    # remove all parentheses
    cleaned = cleaned.replace("(", "").replace(")", "")
    return cleaned

# https://stackoverflow.com/a/76946888
# Return string with the escape sequences at specific indexes to highlight
def highlight_string_at_idxs(string, indexes):
    # hl = "\x1b[38;5;160m"  # 8-bit
    hl = "\x1b[91m"
    reset = "\x1b[0m"
    words_with_hl = []
    for string_idx, word in enumerate(string.split(" ")):
        if string_idx in indexes:
            words_with_hl.append(hl + word + reset)
        else:
            words_with_hl.append(word)
    return " ".join(words_with_hl)


# https://stackoverflow.com/a/76946888
# Return indexes of the additions to s2 compared to s1
def get_indexes_of_additions(s1, s2):
    diffs = list(Differ().compare(s1.split(" "), s2.split(" ")))
    indexes = []
    adj_idx = 0  # Adjust index to compensate for removed words
    for diff_idx, diff in enumerate(diffs):
        if diff[:1] == "+":
            indexes.append(diff_idx - adj_idx)
        elif diff[:1] == "-":
            adj_idx += 1
    return indexes


def check_example(input, output, language):
    print(f"Checking {input} -> {output} ({language})")

    input_path = os.path.join(EXAMPLES, input)
    output_path = os.path.join(EXAMPLES, output)
    with open(output_path, "r") as f:
        expected = f.read()

    # run without solver but with debug to try to catch exception
    eudoxus(input_path, language, StringIO(), False, True)

    # run with solver and without debug to check end-to-end result
    actual = StringIO()
    eudoxus(input_path, language, actual, True, False)
    actual = actual.getvalue()

    if clean(actual) != clean(expected):
        addition_idxs = get_indexes_of_additions(actual, expected)
        diff = highlight_string_at_idxs(expected, addition_idxs)
        assert (
            False
        ), f"\nExpected:\n{expected}\n\nActual:\n{actual}\n\nDifference:\n{diff}"


def test_examples():
    # get all the files in the examples directory
    examples = os.listdir(EXAMPLES)
    # get all the examples that have .input. in them
    inputs = [example for example in examples if ".input." in example]

    for input in inputs:
        base = input.split(".input.")[0]

        output_py = base + ".output.py"
        output_ucl = base + ".output.ucl"

        if output_py in examples:
            check_example(input, output_py, "python")

        if output_ucl in examples:
            check_example(input, output_ucl, "uclid")
