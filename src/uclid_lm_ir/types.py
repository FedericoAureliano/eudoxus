def Integer():
    """Returns a UCLID5 integer type."""
    return "integer"


integer = Integer()
Int = Integer()
int_ = Integer()


def BitVector(width):
    """Returns a UCLID5 bitvector type."""
    return "bv" + str(width)


bitvector = BitVector
bv = BitVector
