import dafnypy
from typing import List, Set

@dafnypy.verify
def cast_to_set(l: List[int]) -> Set[int]:
    return set() if len(l) == 0 else cast_to_set(l[1:]) + {l[0]} 