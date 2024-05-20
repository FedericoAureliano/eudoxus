from dataclasses import dataclass

from eudoxus.ast import expression as e
from eudoxus.ast.node import Identifier
from eudoxus.dfy.ast.list_and_sets import (  # noqa: F401
    EmptyList,
    In,
    ListType,
    Set,
    SetType,
    Slice,
    Subscript,
)


@dataclass(frozen=True)
class IsInstance(e.Expression):
    expr: e.Expression
    type: e.Type


@dataclass(frozen=True)
class Neg(e.Operator):
    pass


@dataclass(frozen=True)
class Power(e.Operator):
    pass


@dataclass(frozen=True)
class Ite(e.Expression):
    condition: e.Expression
    then_expr: e.Expression
    else_expr: e.Expression


@dataclass(frozen=True)
class ForAll(e.Expression):
    variable: Identifier
    domain: e.Expression
    prediate: e.Expression
    condition: e.Expression | None
