import dafnypy
from typing import List

@dafnypy.verify
def sum(n: List[int]) -> int:
    return 0 if len(n) == 0 else n[0] + sum(n[1:]) 