from dataclasses import dataclass
from typing import List

from eudoxus.ast.node import Identifier, Node
from eudoxus.ast.type import Type


@dataclass(frozen=True)
class Expression(Node):
    pass


@dataclass(frozen=True)
class Value(Expression):
    pass


@dataclass(frozen=True)
class EnumValue(Value):
    value: str


@dataclass(frozen=True)
class BooleanValue(Value):
    value: bool


@dataclass(frozen=True)
class IntegerValue(Value):
    value: int


@dataclass(frozen=True)
class BitVectorValue(Value):
    value: int
    width: int


@dataclass(frozen=True)
class ArrayValue(Value):
    default: Expression


@dataclass(frozen=True)
class Operator(Node):
    pass


@dataclass(frozen=True)
class Add(Operator):
    arg1: Expression
    arg2: Expression


@dataclass(frozen=True)
class Subtract(Operator):
    arg1: Expression
    arg2: Expression


@dataclass(frozen=True)
class Multiply(Operator):
    arg1: Expression
    arg2: Expression


@dataclass(frozen=True)
class Divide(Operator):
    arg1: Expression
    arg2: Expression


@dataclass(frozen=True)
class Equal(Operator):
    arg1: Expression
    arg2: Expression


@dataclass(frozen=True)
class NotEqual(Operator):
    arg1: Expression
    arg2: Expression


@dataclass(frozen=True)
class LessThan(Operator):
    arg1: Expression
    arg2: Expression


@dataclass(frozen=True)
class LessThanOrEqual(Operator):
    arg1: Expression
    arg2: Expression


@dataclass(frozen=True)
class GreaterThan(Operator):
    arg1: Expression
    arg2: Expression


@dataclass(frozen=True)
class GreaterThanOrEqual(Operator):
    arg1: Expression
    arg2: Expression


@dataclass(frozen=True)
class And(Operator):
    arg1: Expression
    arg2: Expression


@dataclass(frozen=True)
class Or(Operator):
    arg1: Expression
    arg2: Expression


@dataclass(frozen=True)
class Not(Operator):
    arg: Expression


@dataclass(frozen=True)
class Ite(Operator):
    cond: Expression
    then_: Expression
    else_: Expression


@dataclass(frozen=True)
class Implies(Operator):
    arg1: Expression
    arg2: Expression


@dataclass(frozen=True)
class Quantifier(Operator):
    bound: Identifier
    sort: Type
    body: Expression


@dataclass(frozen=True)
class Forall(Quantifier):
    pass


@dataclass(frozen=True)
class Exists(Quantifier):
    pass


@dataclass(frozen=True)
class FunctionApplication(Expression):
    callee: Identifier
    arguments: List[Expression]


@dataclass(frozen=True)
class RecordSelect(Expression):
    record: Expression
    selector: Identifier


@dataclass(frozen=True)
class ArraySelect(Expression):
    array: Expression
    index: Expression


@dataclass(frozen=True)
class ArrayStore(Expression):
    array: Expression
    index: Expression
    value: Expression
