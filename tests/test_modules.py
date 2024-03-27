import ast

from eudoxus.compiler import compile_to_uclid5
from eudoxus.utils import assert_equal


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
        x' = (x + 1);
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
        x' = (x + 1);
    }
    invariant spec: ((x >= 0) && (x <= 10));
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
        x' = (x + 1);
    }
    invariant spec: ((x >= 0) && (x <= 10));
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
        x' = (x + 1);
    }
    // Comment 5
    invariant spec: ((x >= 0) && (x <= 10));
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
        havoc x;
        assume (x >= 0);
        assert (x >= 110);
    }
    invariant spec: (x >= 100);
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


def test_havoc_assume_assert_alternate():
    code = """
class HavocAssumeAssert(Module):
    def locals(self):
        self.x = Integer()

    def next(self):
        self.x = Any(Integer())
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
        havoc x;
        assume (x >= 0);
        assert (x >= 110);
    }
    invariant spec: (x >= 100);
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
        y' = (x + y);
    }
}
"""
    python = ast.parse(code)
    output = compile_to_uclid5(python)
    assert_equal(output, expected)


def test_assert_with_message():
    code = """
class AssertWithMessage(Module):
    def locals(self):
        self.x = Integer()

    def next(self):
        assert self.x >= 0, "x must be non-negative"
"""
    expected = """
module AssertWithMessage {
    var x : integer;
    next {
        // x must be non-negative
        assert (x >= 0);
    }
}
"""
    python = ast.parse(code)
    output = compile_to_uclid5(python)
    assert_equal(output, expected)


def test_blocks_with_pass():
    code = """
class PassBlocks(Module):
    def proof(self):
        pass
    def next(self):
        pass
    def init(self):
        if True:
            pass
        else:
            pass
"""
    expected = """
module PassBlocks {
}
"""
    python = ast.parse(code)
    output = compile_to_uclid5(python)
    assert_equal(output, expected)


def test_records():
    code = """
class ExtendedModule(Module):
    def types(self):
        self.Pair = Record(a=BitVector(8), b=BitVector(8))
    def locals(self):
        self.pair_var = self.Pair()
    def init(self):
        self.pair_var = self.Pair(a=7, b=2)
    def next(self):
        self.pair_var = self.Pair(a=5, b=3)
    def specification(self):
        return self.pair_var.a > 0 and self.pair_var.b > 0
"""
    expected = """
module ExtendedModule {
    type Pair = record {
        a : bv8,
        b : bv8
    };
    var pair_var : Pair;
    init {
        pair_var = Pair(7, 2);
    }
    next {
        pair_var' = Pair(5, 3);
    }
    invariant spec: ((pair_var.a > 0) && (pair_var.b > 0));
}
"""
    python = ast.parse(code)
    output = compile_to_uclid5(python)
    assert_equal(output, expected)


def test_enumeration():
    code = """
class Enumeration:
    def types(self):
        self.Color = Enumeration('red', 'green', 'blue')
        self.Other = Enumeration(['r', 'g', 'b'])
        self.Other2 = Enumeration(4)
    def locals(self):
        self.color = self.Color()
    def init(self):
        self.color = 'red'
    def next(self):
        self.color = 'green'
    def specification(self):
        return self.color != self.Color.blue
"""
    expected = """
module Enumeration {
    type Color = enum { red, green, blue };
    type Other = enum { r, g, b };
    type Other2 = enum { Other2_v_0, Other2_v_1, Other2_v_2, Other2_v_3 };
    var color : Color;
    init {
        color = red;
    }
    next {
        color' = green;
    }
    invariant spec: (color != blue);
}
"""
    python = ast.parse(code)
    output = compile_to_uclid5(python)
    assert_equal(output, expected)


def test_quantifiers():
    code = """
class Quantifiers(Module):
    def locals(self):
        self.x = Integer()
    def next(self):
        assert exists([x, Integer()], x > 0)
        assert forall([x, Integer()], x < 10)
"""
    expected = """
module Quantifiers {
    var x : integer;
    next {
        assert (exists (x: integer) :: (x > 0));
        assert (forall (x: integer) :: (x < 10));
    }
}
"""
    python = ast.parse(code)
    output = compile_to_uclid5(python)
    assert_equal(output, expected)


def test_multiple_compare():
    code = """
class MultipleCompare(Module):
    def locals(self):
        self.x = Int()
    def next(self):
        assert self.x > self.x + 1 > self.x + 2
"""
    expected = """
module MultipleCompare {
    var x : integer;
    next {
        assert (x > (x + 1)) && ((x + 1) > (x + 2));
    }
}
"""
    python = ast.parse(code)
    output = compile_to_uclid5(python)
    assert_equal(output, expected)
