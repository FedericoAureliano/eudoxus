from uclid_lm_ir import Module, integer_sort


class ModuleWithVarAndInitAndNext(Module):
    def __init__(self):
        self.x = integer_sort()

    def init(self):
        self.x = 0

    def next(self):
        self.x = self.x + 1


def test_simple_execute():
    m = ModuleWithVarAndInitAndNext()
    m.execute(1)
    assert m.x == 1
    m.execute(10)
    assert m.x == 10  # note that execute always starts at init
