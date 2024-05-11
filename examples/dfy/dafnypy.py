values = {}


def verify(func):
    """
    Decorator for verifying the preconditions and postconditions of a function.
    """

    def wrapper(*args, **kwargs):
        # Call the function
        result = func(*args, **kwargs)

        return result

    return wrapper


def requires(expression):
    """
    function for testing the preconditions
    """
    assert expression, "Precondition failed"


def ensures(expression):
    """
    function for testing the postconditions
    """
    assert expression, "Post-condition failed"


def invariant(expression):
    """
    function for testing the invariants
    """
    assert expression, "Invariant failed"


def decreases(expression, loop_id=0):
    """
    function for testing the loop variant
    """
    global values
    assert (
        loop_id not in values.keys() or expression < values[loop_id]
    ), "Loop variant failed"
    values[loop_id] = expression
