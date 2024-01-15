from uclid_lm_ir import Module
from uclid_lm_ir.types import Integer
from uclid_lm_ir.utils import assert_equal


class ModuleM(Module):
    def inputs(self):
        self.a = Integer()

    def outputs(self):
        self.b = Integer()


class main(Module):
    def state(self):
        self.x = Integer()
        self.y = Integer()

    def instances(self):
        self.m = ModuleM(a=self.x, b=self.y)


def test_simple_input_output_module():
    expected = """
module ModuleM {
    input a : integer;
    output b : integer;
}
"""
    output = str(ModuleM())
    assert_equal(output, expected)


def test_simple_instance():
    expected = """
module main {
    var x : integer;
    var y : integer;
    instance m : ModuleM(a : (x), b : (y));
}
"""
    output = str(main())
    assert_equal(output, expected)
