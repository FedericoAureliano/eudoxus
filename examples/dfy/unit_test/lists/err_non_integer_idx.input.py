import dafnypy
from typing import List

@dafnypy.verify
def test_sum(m: float, n: List[int]) -> int:
    result = n[m]
    return result