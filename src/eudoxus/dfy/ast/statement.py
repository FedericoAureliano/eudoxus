from dataclasses import dataclass
from typing import List

from eudoxus.ast import expression as e
from eudoxus.ast import type as t
from eudoxus.ast.node import Identifier
from eudoxus.ast.statement import Block, Statement


@dataclass(frozen=True)
class Requires(Statement):
    condition: e.Expression


@dataclass(frozen=True)
class Invariant(Statement):
    condition: e.Expression


@dataclass(frozen=True)
class Decreases(Statement):
    condition: e.Expression


@dataclass(frozen=True)
class Ensures(Statement):
    condition: e.Expression


@dataclass(frozen=True)
class Return(Statement):
    expr: e.Expression


@dataclass(frozen=True)
class Comment(Statement):
    text: str


@dataclass(frozen=True)
class While(Statement):
    condition: e.Expression
    invariant: List[Invariant]
    decreases: List[Decreases]
    body: Block


@dataclass(frozen=True)
class DeclAssignment(Statement):
    target: Identifier
    value: e.Expression
    ty: t.Type


@dataclass(frozen=True)
class Append(Statement):
    lst: e.Expression
    item: e.Expression
