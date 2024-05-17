from eudoxus.llm.utils import extract_code


def clean(s: str) -> str:
    # remove leading and trailing whitespace
    return s.strip()


def test_simple():
    expected = """class A:
    def __init__(self):
        pass"""
    output = f"```python\n{expected}\n```"
    assert clean(extract_code(output)) == clean(expected)


def test_no_start():
    expected = """class A:
    def __init__(self):
        pass"""
    output = f"{expected}\n```"
    assert clean(extract_code(output)) == clean(expected)


def test_no_end():
    expected = """class A:
    def __init__(self):
        pass"""
    output = f"```python\n{expected}"
    assert clean(extract_code(output)) == clean(expected)


def test_no_start_no_end():
    expected = """class A:
    def __init__(self):
        pass"""
    output = expected
    assert clean(extract_code(output)) == clean(expected)
