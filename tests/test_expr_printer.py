import ast

from uclid_lm_ir.printer import print_uclid5
from uclid_lm_ir.utils import assert_equal


def test_simple_expr():
    python = ast.parse("1 + 2")
    expected = "1 + 2"
    output = print_uclid5(python)
    assert_equal(output, expected)


def test_array_access():
    python = ast.parse("a[1]")
    expected = "a[1]"
    output = print_uclid5(python)
    assert_equal(output, expected)


def test_record_select():
    python = ast.parse("a.b")
    expected = "a.b"
    output = print_uclid5(python)
    assert_equal(output, expected)


def test_multiple_compare():
    python = ast.parse("a < b < c")
    expected = "a < b && b < c"
    output = print_uclid5(python)
    assert_equal(output, expected)


def test_ifexpr():
    python = ast.parse("a if b else c")
    expected = "if (b) then {a} else {c}"
    output = print_uclid5(python)
    assert_equal(output, expected)


def test_assert_stmt():
    python = ast.parse("assert a == b")
    expected = "assert(a == b);"
    output = print_uclid5(python)
    assert_equal(output, expected)


def test_assume_stmt():
    python = ast.parse("assume(a == b)")
    expected = "assume(a == b);"
    output = print_uclid5(python)
    assert_equal(output, expected)


def test_werid_with():
    # We treat with statements as gaurds but it is too broad to parse so we just
    # print a hole for the condition.
    python = """
with ite(true):
    assert true
"""
    python = ast.parse(python)
    expected = "if (??) { assert(true); }"
    output = print_uclid5(python)
    assert_equal(output, expected)
