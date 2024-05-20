import dafnypy

@dafnypy.verify
def power(x: int, pow: int) -> int:
    dafnypy.decreases(pow)
    return 1 if pow == 0 else (power(x, pow - 1) * x if pow >= 1 else 0)