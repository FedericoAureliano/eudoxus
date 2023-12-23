from uclid_lm_ir import Module
from uclid_lm_ir.control import induction
from uclid_lm_ir.types import Integer


def assert_equal(actual: str, expected: str):
    print("Expected:\n")
    print(expected)
    print("\n\nActual:\n")
    print(actual)
    assert actual.split() == expected.split()


class EmptyModule(Module):
    pass


def test_empty_module():
    expected = "module EmptyModule {}"
    assert_equal(str(EmptyModule()), expected)


class ModuleWithVar(Module):
    def state(self):
        self.x = Integer()


def test_module_with_var():
    expected = "module ModuleWithVar {\nvar x : integer;\n}"
    output = str(ModuleWithVar())
    assert_equal(output, expected)


class ModuleWithVarAndInit(Module):
    def state(self):
        self.x = Integer()

    def init(self):
        self.x = 0


def test_module_with_var_and_init():
    expected = """
module ModuleWithVarAndInit {
    var x : integer;
    init {
        x = 0;
    }
}
"""
    output = str(ModuleWithVarAndInit())
    assert_equal(output, expected)


class ModuleWithVarAndInitAndNext(Module):
    def state(self):
        self.x = Integer()

    def init(self):
        self.x = 0

    def next(self):
        self.x = self.x + 1


def test_module_with_var_and_init_and_next():
    expected = """
module ModuleWithVarAndInitAndNext {
    var x : integer;
    init {
        x = 0;
    }
    next {
        x' = x + 1;
    }
}
"""
    output = str(ModuleWithVarAndInitAndNext())
    assert_equal(output, expected)


class ModuleWithVarAndInitAndInvariants(Module):
    def state(self):
        self.x = Integer()

    def init(self):
        self.x = 0

    def next(self):
        self.x = self.x + 1

    def specification(self):
        return self.x >= 0 and self.x <= 10


def test_module_with_var_and_init_and_invariants():
    expected = """
module ModuleWithVarAndInitAndInvariants {
    var x : integer;
    init {
        x = 0;
    }
    next {
        x' = x + 1;
    }
    invariant spec: x >= 0 && x <= 10;
}
"""
    output = str(ModuleWithVarAndInitAndInvariants())
    assert_equal(output, expected)


class ModuleWithVarAndInitAndInvariantsAndControl(Module):
    def state(self):
        self.x = Integer()

    def init(self):
        self.x = 0

    def next(self):
        self.x = self.x + 1

    def specification(self):
        return self.x >= 0 and self.x <= 10

    def proof(self):
        induction(2)


def test_module_with_var_and_init_and_invariants_and_control():
    expected = """
module ModuleWithVarAndInitAndInvariantsAndControl {
    var x : integer;
    init {
        x = 0;
    }
    next {
        x' = x + 1;
    }
    invariant spec: x >= 0 && x <= 10;
    control {
        induction(2);
        check;
        print_results();
    }
}
"""
    output = str(ModuleWithVarAndInitAndInvariantsAndControl())
    assert_equal(output, expected)
