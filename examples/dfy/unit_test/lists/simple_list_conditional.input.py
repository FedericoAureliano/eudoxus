import dafnypy
from typing import List

@dafnypy.verify
def test_sum(m: int, n: List[int]) -> int:
    result = n[m] + n[m + 1]
    if n[m] < 0: 
        result = 0
    return result