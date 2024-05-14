from dataclasses import dataclass

from eudoxus.ast import expression as e


@dataclass(frozen=True)
class Ite(e.Expression):
    condition: e.Expression
    then_expr: e.Expression
    else_expr: e.Expression


@dataclass(frozen=True)
class Slice(e.Expression):
    start: e.Expression | None
    end: e.Expression | None
    step: e.Expression | None


@dataclass(frozen=True)
class Subscript(e.Expression):
    list_value: e.Expression
    subscript: e.Expression | Slice
