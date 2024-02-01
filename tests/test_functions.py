import ast

from uclid_lm_ir.compiler import compile_to_uclid5
from uclid_lm_ir.utils import assert_equal


def test_simple_function():
    code = """
class Main(Module):
    def functions(self):
        self.f = Function(Integer(), Array(Bitvector(8), Integer()))
"""
    expected = """
module Main {
    function f(integer) : [bv8]integer;
}
"""
    python = ast.parse(code)
    output = compile_to_uclid5(python)
    assert_equal(output, expected)


def test_three_functions():
    code = """
class Main(Module):
    def functions(self):
        self.f = Function(Integer(), Real(), Array(Bitvector(8), Integer()))
        self.g = Function(Bitvector(8), Bitvector(8))
        self.h = Function(Integer())
"""
    expected = """
module Main {
    function f(integer, real) : [bv8]integer;
    function g(bv8) : bv8;
    function h() : integer;
}
"""
    python = ast.parse(code)
    output = compile_to_uclid5(python)
    assert_equal(output, expected)


def test_function_use():
    code = """
class Main(Module):
    def functions(self):
        self.f = Function(Integer(), Real(), Integer())
    def locals(self):
        self.x = Integer()
    def init(self):
        self.x = self.f(0, 0.0);
"""
    expected = """
module Main {
    function f(integer, real) : integer;
    var x : integer;
    init {
        x = f(0, 0.0);
    }
}
"""
    python = ast.parse(code)
    output = compile_to_uclid5(python)
    assert_equal(output, expected)
