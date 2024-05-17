from dataclasses import dataclass
from typing import List

from eudoxus.ast import expression as e
from eudoxus.ast.type import Type


@dataclass(frozen=True)
class ListType(Type):
    element: Type


@dataclass(frozen=True)
class SetType(Type):
    element: Type


@dataclass(frozen=True)
class Slice(e.Expression):
    start: e.Expression | None
    end: e.Expression | None
    step: e.Expression | None


@dataclass(frozen=True)
class Subscript(e.Expression):
    list_value: e.Expression
    subscript: e.Expression | Slice


@dataclass(frozen=True)
class EmptyList(e.Expression):
    pass


@dataclass(frozen=True)
class In(e.Operator):
    pass


@dataclass(frozen=True)
class Set(e.Expression):
    content: List[e.Expression] | None
