from dataclasses import dataclass
from typing import List, Tuple

from eudoxus.ast.node import Identifier, Node


@dataclass(frozen=True)
class Type(Node):
    pass


@dataclass(frozen=True)
class Boolean(Type):
    pass


@dataclass(frozen=True)
class Integer(Type):
    pass


@dataclass(frozen=True)
class Float(Type):
    pass


@dataclass(frozen=True)
class BitVector(Type):
    width: int


@dataclass(frozen=True)
class Function(Type):
    domain: list[Type]
    codomain: Type


@dataclass(frozen=True)
class Array(Type):
    index: Type
    element: Type


@dataclass(frozen=True)
class Synonym(Type):
    name: Identifier


@dataclass(frozen=True)
class Enumeration(Type):
    values: list[Identifier]


@dataclass(frozen=True)
class Record(Type):
    fields: List[Tuple[Identifier, Type]]
