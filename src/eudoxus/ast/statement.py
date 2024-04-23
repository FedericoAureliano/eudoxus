from dataclasses import dataclass
from typing import List, Tuple

import eudoxus.ast.expression as e
import eudoxus.ast.type as t
from eudoxus.ast.node import Identifier, Node


@dataclass(frozen=True)
class Statement(Node):
    pass


@dataclass(frozen=True)
class Block(Statement):
    statements: list[Statement]


@dataclass(frozen=True)
class Assignment(Statement):
    target: e.Expression
    value: e.Expression


@dataclass(frozen=True)
class If(Statement):
    condition: e.Expression
    then_branch: Block
    else_branch: Block


@dataclass(frozen=True)
class Assume(Statement):
    condition: e.Expression


@dataclass(frozen=True)
class Assert(Statement):
    condition: e.Expression


@dataclass(frozen=True)
class Skip(Statement):
    pass


@dataclass(frozen=True)
class Havoc(Statement):
    target: Identifier


@dataclass(frozen=True)
class Declaration(Statement):
    pass


@dataclass(frozen=True)
class Variable(Declaration):
    target: Identifier
    type: t.Type


@dataclass(frozen=True)
class Local(Variable):
    pass


@dataclass(frozen=True)
class Input(Variable):
    pass


@dataclass(frozen=True)
class Output(Variable):
    pass


@dataclass(frozen=True)
class SharedVar(Variable):
    pass


@dataclass(frozen=True)
class Constant(Variable):
    value: e.Expression


@dataclass(frozen=True)
class Type(Declaration):
    target: Identifier
    type: t.Type | None


@dataclass(frozen=True)
class Instance(Declaration):
    target: Identifier
    module: Identifier
    arguments: List[Tuple[Identifier, e.Expression]]
