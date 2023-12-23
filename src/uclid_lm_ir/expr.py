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


def Exists(vars, expr):
    """Construct an exists expression."""
    return f"exists ({vars}) :: {expr}"


exists = Exists
EXISTS = Exists
