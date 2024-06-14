import dafnypy
from typing import List

@dafnypy.verify
def test_div(m: int, n) -> int:
    result = m // n
    return result