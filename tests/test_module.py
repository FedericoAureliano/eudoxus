from uclid_lm_ir import Module, integer_sort


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
    def __init__(self):
        self.x = integer_sort()


def test_module_with_var():
    expected = "module ModuleWithVar {\nvar x : integer;\n}"
    output = str(ModuleWithVar())
    assert_equal(output, expected)


class ModuleWithVarAndInit(Module):
    def __init__(self):
        self.x = integer_sort()

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
    def __init__(self):
        self.x = integer_sort()

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
