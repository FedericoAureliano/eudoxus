import dafnypy

@dafnypy.verify
def abs(x: int) -> int:
    return x if x >= 0 else -x
