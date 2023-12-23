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


def Boolean():
    """Returns a UCLID5 boolean type."""
    return "boolean"


bool_ = Boolean()
Bool = Boolean()
boolean = Boolean()


def Enum(*args):
    """Returns a UCLID5 enum type."""
    return "enum {" + ", ".join(args) + "}"


enum = Enum
enumerated_type = Enum
enumerated = Enum


def Record(names, types):
    """Returns a UCLID5 record type."""
    zipped = zip(names, types)
    return "record {" + ", ".join([name + ": " + type for name, type in zipped]) + "}"


record = Record
struct = Record
struct_type = Record
struct_ = Record


def Array(index_type, element_type):
    """Returns a UCLID5 array type."""
    return "[" + index_type + "] of " + element_type


array = Array
