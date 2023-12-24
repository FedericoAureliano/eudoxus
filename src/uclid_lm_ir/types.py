def Integer(*args, **kwargs):
    """Returns a UCLID5 integer type."""
    if len(args) >= 1:
        return args[0]
    if "width" in kwargs:
        return BitVector(kwargs["width"])
    if "value" in kwargs:
        return kwargs["value"]
    if "val" in kwargs:
        return kwargs["val"]
    return "integer"


integer = Integer()
Int = Integer()
int_ = Integer()


def BitVector(*args, **kwargs):
    """Returns a UCLID5 bitvector type."""
    if len(args) >= 1:
        width = args[0]
    if "width" in kwargs:
        width = kwargs["width"]
    if "value" in kwargs:
        return kwargs["value"]
    if "val" in kwargs:
        return kwargs["val"]
    if "size" in kwargs:
        width = kwargs["size"]
    return "bv" + str(width)


bitvector = BitVector
bv = BitVector


def Boolean(*args, **kwargs):
    """Returns a UCLID5 boolean type."""
    if len(args) >= 1:
        return args[0]
    if "value" in kwargs:
        return kwargs["value"]
    if "val" in kwargs:
        return kwargs["val"]
    return "boolean"


bool_ = Boolean()
Bool = Boolean()
boolean = Boolean()


def Enum(*args):
    """Returns a UCLID5 enum type."""
    if len(args) == 2 and " " not in args[0] and " " in args[1]:
        cases = args[1].split()
        return "enum { " + ", ".join(cases) + " }"
    return "enum { " + ", ".join(args) + " }"


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


def Array(*args, **kwargs):
    """Returns a UCLID5 array type."""
    if len(args) >= 1:
        index_type = args[0]
    if len(args) >= 2:
        element_type = args[1]
    if "index" in kwargs:
        index_type = kwargs["index"]
    if "value" in kwargs:
        element_type = kwargs["value"]
    if "index_type" in kwargs:
        index_type = kwargs["index_type"]
    if "element_type" in kwargs:
        element_type = kwargs["element_type"]
    if "value_type" in kwargs:
        element_type = kwargs["value_type"]
    if "value" in kwargs:
        element_type = kwargs["value"]
    if "val" in kwargs:
        element_type = kwargs["val"]
    if "in" in kwargs:
        index_type = kwargs["in"]
    if "of" in kwargs:
        element_type = kwargs["of"]
    return "[" + index_type + "]" + element_type


array = Array
