from dataclasses import dataclass

from eudoxus.ast.node import Identifier, Node
from eudoxus.ast.type import Type


@dataclass(frozen=True)
class Expression(Node):
    pass


@dataclass(frozen=True)
class Constant(Expression):
    pass


@dataclass(frozen=True)
class Boolean(Constant):
    value: bool


@dataclass(frozen=True)
class Integer(Constant):
    value: int


@dataclass(frozen=True)
class Float(Constant):
    value: float


@dataclass(frozen=True)
class BitVector(Constant):
    value: int
    width: int


@dataclass(frozen=True)
class Array(Constant):
    default: Expression


@dataclass(frozen=True)
class Variant(Constant):
    value: str


@dataclass(frozen=True)
class Operator(Node):
    pass


@dataclass(frozen=True)
class Add(Operator):
    pass


@dataclass(frozen=True)
class Subtract(Operator):
    pass


@dataclass(frozen=True)
class Multiply(Operator):
    pass


@dataclass(frozen=True)
class Divide(Operator):
    pass


@dataclass(frozen=True)
class Modulo(Operator):
    pass


@dataclass(frozen=True)
class Equal(Operator):
    pass


@dataclass(frozen=True)
class NotEqual(Operator):
    pass


@dataclass(frozen=True)
class LessThan(Operator):
    pass


@dataclass(frozen=True)
class LessThanOrEqual(Operator):
    pass


@dataclass(frozen=True)
class GreaterThan(Operator):
    pass


@dataclass(frozen=True)
class GreaterThanOrEqual(Operator):
    pass


@dataclass(frozen=True)
class And(Operator):
    pass


@dataclass(frozen=True)
class Or(Operator):
    pass


@dataclass(frozen=True)
class Not(Operator):
    pass


@dataclass(frozen=True)
class Ite(Operator):
    pass


@dataclass(frozen=True)
class Implies(Operator):
    pass


@dataclass(frozen=True)
class Quantifier(Operator):
    bindings: list[tuple[Identifier, Type]]


@dataclass(frozen=True)
class Forall(Quantifier):
    pass


@dataclass(frozen=True)
class Exists(Quantifier):
    pass


@dataclass(frozen=True)
class Application(Expression):
    callee: Identifier | Operator
    arguments: list[Expression]


@dataclass(frozen=True)
class Selection(Expression):
    record: Expression
    selector: Identifier
