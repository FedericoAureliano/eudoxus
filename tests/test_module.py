from uclid_lm_ir import Module, integer_sort


class EmptyModule(Module):
    pass


def test_empty_module():
    expected = "module EmptyModule {}"
    assert str(EmptyModule()).split() == expected.split()


class ModuleWithVar(Module):
    def __init__(self):
        self.x = integer_sort()


def test_module_with_var():
    expected = "module ModuleWithVar {\nvar x : integer;\n}"
    output = str(ModuleWithVar())
    print(output)
    assert output.split() == expected.split()
