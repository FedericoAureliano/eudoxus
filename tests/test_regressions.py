import ast

from uclid_lm_ir.printer import print_uclid5
from uclid_lm_ir.utils import assert_equal


def test_regression_1():
    code = """
class IntersectionModule(Module):
    def types(self):
        self.CarState = Enum('CarState', 'moving stopped')
        self.LightState = Enum('LightState', 'red green')

    def state(self):
        self.car1 = self.CarState
        self.car2 = self.CarState
        self.light1 = self.LightState
        self.light2 = self.LightState

    def init(self):
        self.car1 = stopped
        self.car2 = stopped
        self.light1 = red
        self.light2 = red

    def next(self):
        if self.light1 == green:
            self.car1 = moving
        else:
            self.car1 = stopped
"""

    expected = """
module IntersectionModule {
    type CarState = enum { moving, stopped };
    type LightState = enum { red, green };
    var car1 : CarState;
    var car2 : CarState;
    var light1 : LightState;
    var light2 : LightState;

    init {
        car1 = stopped;
        car2 = stopped;
        light1 = red;
        light2 = red;
    }

    next {
        if (light1 == green) {
            car1' = moving;
        } else {
            car1' = stopped;
        }
    }
}
"""
    python = ast.parse(code)
    output = print_uclid5(python)
    assert_equal(output, expected)


def test_regression_2():
    code = """
class Module:
    def types(self):
        self.T = BitVector(8)

    def state(self):
        self.x = Array(index=BitVector(8), value=self.T)
"""

    expected = """
module Module {
    type T = bv8;
    var x : [bv8]T;
}
"""
    python = ast.parse(code)
    output = print_uclid5(python)
    assert_equal(output, expected)
