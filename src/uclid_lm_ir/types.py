def Integer():
    """
    Returns a UCLID5 integer type.
    """
    return "integer"


def BitVector(width):
    """
    Returns a UCLID5 bitvector type.
    """
    return "bv" + str(width)
