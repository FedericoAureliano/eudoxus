import ast

from eudoxus.compiler import compile_to_uclid5
from eudoxus.utils import assert_equal


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
    output = compile_to_uclid5(python)
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
    output = compile_to_uclid5(python)
    assert_equal(output, expected)


def test_instance_as_variable():
    code = """
class A(Module):
    pass
class main(Module):
    def locals(self):
        self.x = Integer()
        self.y = Integer()
        self.m = A()
"""
    expected = """
module A {
}
module main {
    var x : integer;
    var y : integer;
    // To declare an instance you must use the 'instance' keyword.
    var m : ??;
}
"""
    python = ast.parse(code)
    output = compile_to_uclid5(python)
    assert_equal(output, expected)
