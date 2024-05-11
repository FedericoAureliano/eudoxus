import dafnypy


@dafnypy.verify
def increment(m: int, n: int) -> int:
    # Precondition: requires statements for precondition
    dafnypy.requires(m <= n)

    i = m
    # Main function body
    while i < n:
        # Invariant: ensures that i is bounded
        dafnypy.invariant(0 <= i)
        dafnypy.invariant(i <= n)
        i += 1
    result = i

    # Post-condition: ensures statements for post-condition
    dafnypy.ensures(result == n)
    return result


print(increment(1, 5))
increment(5, 1)
