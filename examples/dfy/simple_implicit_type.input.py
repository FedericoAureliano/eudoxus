import dafnypy
from typing import List

@dafnypy.verify
def sum(m: int, n) -> int:
    dafnypy.requires(m >= 0)
    dafnypy.requires(n >= 0)
    result = m + n
    dafnypy.ensures(result == m + n)
    return result