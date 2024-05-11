from dataclasses import dataclass

from eudoxus.ast.type import Type


@dataclass(frozen=True)
class List(Type):
    element: Type
