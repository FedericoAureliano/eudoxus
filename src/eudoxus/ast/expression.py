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
    value: Identifier


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
class Add(Expression):
    arg1: Expression
    arg2: Expression


@dataclass(frozen=True)
class Subtract(Expression):
    arg1: Expression
    arg2: Expression


@dataclass(frozen=True)
class Multiply(Expression):
    arg1: Expression
    arg2: Expression


@dataclass(frozen=True)
class Divide(Expression):
    arg1: Expression
    arg2: Expression


@dataclass(frozen=True)
class Equal(Expression):
    arg1: Expression
    arg2: Expression


@dataclass(frozen=True)
class NotEqual(Expression):
    arg1: Expression
    arg2: Expression


@dataclass(frozen=True)
class LessThan(Expression):
    arg1: Expression
    arg2: Expression


@dataclass(frozen=True)
class LessThanOrEqual(Expression):
    arg1: Expression
    arg2: Expression


@dataclass(frozen=True)
class GreaterThan(Expression):
    arg1: Expression
    arg2: Expression


@dataclass(frozen=True)
class GreaterThanOrEqual(Expression):
    arg1: Expression
    arg2: Expression


@dataclass(frozen=True)
class And(Expression):
    arg1: Expression
    arg2: Expression


@dataclass(frozen=True)
class Or(Expression):
    arg1: Expression
    arg2: Expression


@dataclass(frozen=True)
class Not(Expression):
    arg: Expression


@dataclass(frozen=True)
class Ite(Expression):
    cond: Expression
    then_: Expression
    else_: Expression


@dataclass(frozen=True)
class Implies(Expression):
    arg1: Expression
    arg2: Expression


@dataclass(frozen=True)
class Quantifier(Expression):
    pass


@dataclass(frozen=True)
class Forall(Quantifier):
    bound: Identifier
    sort: Type
    body: Expression


@dataclass(frozen=True)
class Exists(Quantifier):
    bound: Identifier
    sort: Type
    body: Expression


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
