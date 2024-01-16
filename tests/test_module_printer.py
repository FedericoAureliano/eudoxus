from uclid_lm_ir import Module
from uclid_lm_ir.control import induction
from uclid_lm_ir.type import BitVector, Integer
from uclid_lm_ir.utils import assert_equal


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


class ModuleWithTypeDecls(Module):
    def types(self):
        self.T = Integer()
        self.U = BitVector(32)


def test_module_with_type_decls():
    expected = """
module ModuleWithTypeDecls {
    type T = integer;
    type U = bv32;
}
"""
    output = str(ModuleWithTypeDecls())
    assert_equal(output, expected)


class ModuleWithTypeDeclsAndUses(Module):
    def types(self):
        self.T = Integer()
        self.U = BitVector(32)

    def state(self):
        self.x = self.T()
        self.y = self.U()


def test_module_with_type_decls_and_uses():
    expected = """
module ModuleWithTypeDeclsAndUses {
    type T = integer;
    type U = bv32;
    var x : T;
    var y : U;
}
"""
    output = str(ModuleWithTypeDeclsAndUses())
    assert_equal(output, expected)


class ModuleWithComments(Module):
    """Comment 0"""

    def types(self):
        """Comment 1"""
        self.T = Integer()

    def state(self):
        """Comment 2"""
        self.x = self.T

    def init(self):
        """Comment 3"""
        self.x = 0

    def next(self):
        """Comment 4"""
        self.x = self.x + 1

    def specification(self):
        """Comment 5"""
        return self.x >= 0 and self.x <= 10

    def proof(self):
        """Comment 6"""
        induction(2)


def test_module_with_comments():
    expected = """
module ModuleWithComments {
    // Comment 0
    // Comment 1
    type T = integer;
    // Comment 2
    var x : T;
    init {
        // Comment 3
        x = 0;
    }
    next {
        // Comment 4
        x' = x + 1;
    }
    // Comment 5
    invariant spec: x >= 0 && x <= 10;
    control {
        // Comment 6
        induction(2);
        check;
        print_results();
    }
}
"""
    output = str(ModuleWithComments())
    assert_equal(output, expected)
