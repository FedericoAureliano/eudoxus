import dafnypy
from typing import List

@dafnypy.verify
def test_sum(m: int, n: List[int]) -> int:
    dafnypy.requires(m > 0)
    dafnypy.requires(len(n) > m + 1)
    result = n[m] + n[m + 1]
    return result