def Ite(test, then, els):
    """Construct an if-then-else expression."""
    return f"if ({test}) {{\n{then}\n}} else {{\n{els}\n}}"


ite = Ite
ITE = Ite
If = Ite
IF = Ite
if_ = Ite
IF_ = Ite
if_then_else = Ite
IF_THEN_ELSE = Ite
IfThenElse = Ite
