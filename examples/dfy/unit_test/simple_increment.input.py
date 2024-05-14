import dafnypy
from typing import List

@dafnypy.verify
def test_sum(m: int, n: List[int]) -> int:
    result += 1
    return result