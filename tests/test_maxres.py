import z3

from eudoxus.ast.node import Position
from eudoxus.checker.interface import Checker


def test_maxres():
    # Example from https://cdn.aaai.org/ojs/9124/9124-13-12652-1-2-20201228.pdf
    varss = [z3.Bool(f"x{i}") for i in range(1, 6)]

    mychecker = Checker()

    mychecker.soft_constraints = {Position(i): [varss[i - 1]] for i in range(1, 6)}

    mychecker.hard_constraints = [
        z3.Not(z3.And(varss[i], varss[j])) for i in range(5) for j in range(i + 1, 5)
    ]

    actual = mychecker.solve_maxres()[0]
    expected = [Position(i) for i in [1, 2, 4, 5]]

    if actual != expected:
        assert False, f"\nExpected:\n{expected}\n\nActual:\n{actual}"
