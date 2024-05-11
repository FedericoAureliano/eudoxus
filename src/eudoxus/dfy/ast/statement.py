from dataclasses import dataclass

from eudoxus.ast import expression as e
from eudoxus.ast.statement import Statement


@dataclass(frozen=True)
class Requires(Statement):
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
