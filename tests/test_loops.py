import ast

from uclid_lm_ir.compiler import compile_to_uclid5
from uclid_lm_ir.utils import assert_equal


def test_simple_for():
    code = """
class Main(Module):
    def locals(self):
        self.x = Integer()
    def init(self):
        for i in range(10):
            self.x = i
"""
    expected = """
module Main {
    var x : integer;
    init {
        for i in range(0, 9) {
            x = i;
        }
    }
}
"""
    python = ast.parse(code)
    output = compile_to_uclid5(python)
    assert_equal(output, expected)
