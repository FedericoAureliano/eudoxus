import ast

from uclid_lm_ir.compiler import compile_to_uclid5
from uclid_lm_ir.utils import assert_equal


def test_empty_module():
    code = """
class EmptyModule(Module):
    pass
"""
    expected = "module EmptyModule { }"
    python = ast.parse(code)
    output = compile_to_uclid5(python)
    assert_equal(output, expected)


def test_module_with_var():
    code = """
class ModuleWithVar(Module):
    def locals(self):
        self.x = Integer()
"""
    expected = "module ModuleWithVar {\nvar x : integer;\n}"
    python = ast.parse(code)
    output = compile_to_uclid5(python)
    assert_equal(output, expected)


def test_module_with_var_and_init():
    code = """
class ModuleWithVarAndInit(Module):
    def locals(self):
        self.x = Integer()

    def init(self):
        self.x = 0
"""
    expected = """
module ModuleWithVarAndInit {
    var x : integer;
    init {
        x = 0;
    }
}
"""
    python = ast.parse(code)
    output = compile_to_uclid5(python)
    assert_equal(output, expected)


def test_module_with_var_and_init_and_next():
    code = """
class ModuleWithVarAndInitAndNext(Module):
    def locals(self):
        self.x = Integer()

    def init(self):
        self.x = 0

    def next(self):
        self.x = self.x + 1
"""
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
    python = ast.parse(code)
    output = compile_to_uclid5(python)
    assert_equal(output, expected)


def test_module_with_var_and_init_and_invariants():
    code = """
class ModuleWithVarAndInitAndInvariants(Module):
    def locals(self):
        self.x = Integer()

    def init(self):
        self.x = 0

    def next(self):
        self.x = self.x + 1

    def specification(self):
        return self.x >= 0 and self.x <= 10
"""
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
    python = ast.parse(code)
    output = compile_to_uclid5(python)
    assert_equal(output, expected)


def test_module_with_var_and_init_and_invariants_and_control():
    code = """
class ModuleWithVarAndInitAndInvariantsAndControl(Module):
    def locals(self):
        self.x = Integer()

    def init(self):
        self.x = 0

    def next(self):
        self.x = self.x + 1

    def specification(self):
        return self.x >= 0 and self.x <= 10

    def proof(self):
        induction(2)
"""
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
    python = ast.parse(code)
    output = compile_to_uclid5(python)
    assert_equal(output, expected)


def test_module_with_type_decls():
    code = """
class ModuleWithTypeDecls(Module):
    def types(self):
        self.T = Integer()
        self.U = BitVector(32)
"""
    expected = """
module ModuleWithTypeDecls {
    type T = integer;
    type U = bv32;
}
"""
    python = ast.parse(code)
    output = compile_to_uclid5(python)
    assert_equal(output, expected)


def test_module_with_type_decls_and_uses():
    code = """
class ModuleWithTypeDeclsAndUses(Module):
    def types(self):
        self.T = Integer()
        self.U = BitVector(32)

    def locals(self):
        self.x = self.T()
        self.y = self.U()
"""
    expected = """
module ModuleWithTypeDeclsAndUses {
    type T = integer;
    type U = bv32;
    var x : T;
    var y : U;
}
"""
    python = ast.parse(code)
    output = compile_to_uclid5(python)
    assert_equal(output, expected)


def test_module_with_comments():
    code = '''
class ModuleWithComments(Module):
    """Comment 0"""

    def types(self):
        """Comment 1"""
        self.T = Integer()

    def locals(self):
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
'''
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
    python = ast.parse(code)
    output = compile_to_uclid5(python)
    assert_equal(output, expected)


def test_havoc_assume_assert():
    code = """
class HavocAssumeAssert(Module):
    def locals(self):
        self.x = Integer()

    def next(self):
        havoc(self.x)
        assume(self.x >= 0)
        assert self.x >= 110

    def specification(self):
        return self.x >= 100

    def proof(self):
        bmc(2)
"""
    expected = """
module HavocAssumeAssert {
    var x : integer;
    next {
        havoc(x);
        assume(x >= 0);
        assert(x >= 110);
    }
    invariant spec: x >= 100;
    control {
        bmc(2);
        check;
        print_results();
    }
}
"""
    python = ast.parse(code)
    output = compile_to_uclid5(python)
    assert_equal(output, expected)


def test_parallel_assign():
    code = """
class MultipleAssign(Module):
    def locals(self):
        self.x = Integer()
        self.y = Integer()

    def next(self):
        self.x, self.y = self.y, self.x + self.y
"""
    expected = """
module MultipleAssign {
    var x : integer;
    var y : integer;
    next {
        x' = y;
        y' = x + y;
    }
}
"""
    python = ast.parse(code)
    output = compile_to_uclid5(python)
    assert_equal(output, expected)
