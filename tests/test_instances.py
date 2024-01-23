import ast

from uclid_lm_ir.printer import print_uclid5
from uclid_lm_ir.utils import assert_equal


def test_simple_input_output_module():
    code = """
class ModuleM(Module):
    def inputs(self):
        self.a = Integer()

    def outputs(self):
        self.b = Integer()
"""
    expected = """
module ModuleM {
    input a : integer;
    output b : integer;
}
"""
    python = ast.parse(code)
    output = print_uclid5(python)
    assert_equal(output, expected)


def test_simple_instance():
    code = """
class main(Module):
    def locals(self):
        self.x = Integer()
        self.y = Integer()

    def instances(self):
        self.m = ModuleM(a=self.x, b=self.y)
"""
    expected = """
module main {
    var x : integer;
    var y : integer;
    instance m : ModuleM(a : (x), b : (y));
}
"""
    python = ast.parse(code)
    output = print_uclid5(python)
    assert_equal(output, expected)
