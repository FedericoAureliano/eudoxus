def Ite(test, then, els):
    """Construct an if-then-else expression."""
    return f"if ({test}) then {{{then}}} else {{{els}}}"


ite = Ite
ITE = Ite
If = Ite
IF = Ite
if_ = Ite
IF_ = Ite
if_then_else = Ite
IF_THEN_ELSE = Ite
IfThenElse = Ite
If_then_else = Ite


def And(*args):
    """Construct an and expression."""
    return " && ".join(args)


and_ = And
AND = And


def Or(*args):
    """Construct an or expression."""
    return " || ".join(args)


or_ = Or
OR = Or


def Not(arg):
    """Construct a not expression."""
    return f"!{arg}"


not_ = Not
NOT = Not


def Implies(lhs, rhs):
    """Construct an implies expression."""
    return f"{lhs} ==> {rhs}"


implies = Implies
IMPLIES = Implies
Implies_ = Implies
implies_ = Implies
impl = Implies
IMPL = Implies


def Equals(lhs, rhs):
    """Construct an iff expression."""
    return f"{lhs} == {rhs}"


iff = Equals
IFF = Equals
equals = Equals
EQUALS = Equals
eq = Equals
EQ = Equals


def Forall(vars, expr):
    """Construct a forall expression."""
    return f"forall ({vars}) :: {expr}"


forall = Forall
FORALL = Forall
ForAll = Forall
Forall_ = Forall
forall_ = Forall


def Exists(vars, expr):
    """Construct an exists expression."""
    return f"exists ({vars}) :: {expr}"


exists = Exists
EXISTS = Exists
Exist_ = Exists
exist_ = Exists


def UnsignedLessThan(lhs, rhs):
    """Construct an unsigned less than expression."""
    return f"{lhs} < {rhs}"


ult = UnsignedLessThan
ULT = UnsignedLessThan
UnsignedLT = UnsignedLessThan
Ult = UnsignedLessThan
unsigned_less_than = UnsignedLessThan
Unsigned_less_than = UnsignedLessThan


def UnsignedLessThanEquals(lhs, rhs):
    """Construct an unsigned less than or equals expression."""
    return f"{lhs} <= {rhs}"


ule = UnsignedLessThanEquals
ULE = UnsignedLessThanEquals
UnsignedLTE = UnsignedLessThanEquals
Ule = UnsignedLessThanEquals
unsigned_less_than_equals = UnsignedLessThanEquals
Unsigned_less_than_equals = UnsignedLessThanEquals
Ulte = UnsignedLessThanEquals
ulte = UnsignedLessThanEquals


def UnsignedGreaterThan(lhs, rhs):
    """Construct an unsigned greater than expression."""
    return f"{lhs} > {rhs}"


ugt = UnsignedGreaterThan
UGT = UnsignedGreaterThan
UnsignedGT = UnsignedGreaterThan
Ugt = UnsignedGreaterThan
unsigned_greater_than = UnsignedGreaterThan
Unsigned_greater_than = UnsignedGreaterThan


def UnsignedGreaterThanEquals(lhs, rhs):
    """Construct an unsigned greater than or equals expression."""
    return f"{lhs} >= {rhs}"


uge = UnsignedGreaterThanEquals
UGE = UnsignedGreaterThanEquals
UnsignedGTE = UnsignedGreaterThanEquals
Uge = UnsignedGreaterThanEquals
unsigned_greater_than_equals = UnsignedGreaterThanEquals
Unsigned_greater_than_equals = UnsignedGreaterThanEquals
Ugte = UnsignedGreaterThanEquals
ugte = UnsignedGreaterThanEquals


def Havoc(var):
    """Construct a havoc expression."""
    return f"havoc {var}"


havoc = Havoc
HAVOC = Havoc


def Fresh(*args, **kwargs):
    """Construct a fresh expression."""
    return "*"


fresh = Fresh
FRESH = Fresh

freshInt = Fresh
fresh_int = Fresh
FreshInt = Fresh
Fresh_int = Fresh

freshBV = Fresh
fresh_bv = Fresh
FreshBV = Fresh
Fresh_bv = Fresh
FreshBitVector = Fresh
Fresh_bit_vector = Fresh
freshBitVector = Fresh
fresh_bit_vector = Fresh
fresh_bitvector = Fresh

freshBool = Fresh
Fresh_bool = Fresh
FreshBool = Fresh
fresh_bool = Fresh

freshArray = Fresh
fresh_array = Fresh
FreshArray = Fresh
Fresh_array = Fresh

FreshVar = Fresh
Fresh_var = Fresh
freshVar = Fresh
fresh_var = Fresh


def Update(array, index, value):
    """Construct an update expression."""
    return f"{array}[{index} -> {value}]"


update = Update
UPDATE = Update


def Select(array, index):
    """Construct a select expression."""
    return f"{array}[{index}]"


select = Select
SELECT = Select
get = Select
GET = Select
Get = Select


def ConstArray(index_type, value):
    """Construct a constant array expression."""
    return f"const({index_type}, {value})"


const_array = ConstArray
CONST_ARRAY = ConstArray
constArray = ConstArray
const = ConstArray
CONST = ConstArray
Const = ConstArray
