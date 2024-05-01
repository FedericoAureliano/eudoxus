from dataclasses import dataclass
from typing import List, Tuple

from eudoxus.ast.node import Identifier, Node


@dataclass(frozen=True)
class Type(Node):
    pass


@dataclass(frozen=True)
class BooleanType(Type):
    pass


@dataclass(frozen=True)
class IntegerType(Type):
    pass


@dataclass(frozen=True)
class BitVectorType(Type):
    width: int


@dataclass(frozen=True)
class FunctionType(Type):
    domain: List[Type]
    codomain: Type


@dataclass(frozen=True)
class ArrayType(Type):
    index: Type
    element: Type


@dataclass(frozen=True)
class SynonymType(Type):
    name: Identifier


@dataclass(frozen=True)
class EnumeratedType(Type):
    values: List[Identifier]


@dataclass(frozen=True)
class RecordType(Type):
    fields: List[Tuple[Identifier, Type]]


@dataclass(frozen=True)
class HoleType(Type):
    # just in case we try to treat a hole as an identifier
    @property
    def name(self) -> str:
        return "??"
