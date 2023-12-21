from uclid_lm_ir import Module


class EmptyModule(Module):
    pass


def test_empty_module():
    expected = "module EmptyModule {\n\n}"
    assert str(EmptyModule()) == expected
