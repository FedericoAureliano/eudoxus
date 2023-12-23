import ast

from uclid_lm_ir.printer import print_uclid5


def test_simple_expr():
    python = ast.parse("1 + 2")
    expected = "1 + 2"
    output = print_uclid5(python)
    assert output == expected


def test_array_access():
    python = ast.parse("a[1]")
    expected = "a[1]"
    output = print_uclid5(python)
    assert output == expected


def test_record_select():
    python = ast.parse("a.b")
    expected = "a.b"
    output = print_uclid5(python)
    assert output == expected


def test_multiple_compare():
    python = ast.parse("a < b < c")
    expected = "a < b && b < c"
    output = print_uclid5(python)
    assert output == expected
