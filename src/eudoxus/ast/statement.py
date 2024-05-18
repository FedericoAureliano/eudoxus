from dataclasses import dataclass
from typing import List, Tuple

import eudoxus.ast.expression as e
import eudoxus.ast.type as t
from eudoxus.ast.node import Identifier, Node


@dataclass(frozen=True)
class Statement(Node):
    def is_empty(self):
        return False


@dataclass(frozen=True)
class Block(Statement):
    statements: List[Statement]

    def is_empty(self):
        return len(self.statements) == 0


@dataclass(frozen=True)
class Assignment(Statement):
    target: e.Expression
    value: e.Expression


@dataclass(frozen=True)
class If(Statement):
    condition: e.Expression
    then_branch: Statement
    else_branch: Statement


@dataclass(frozen=True)
class Assume(Statement):
    condition: e.Expression


@dataclass(frozen=True)
class Assert(Statement):
    condition: e.Expression


@dataclass(frozen=True)
class Havoc(Statement):
    target: Identifier


@dataclass(frozen=True)
class Next(Statement):
    instance: Identifier


@dataclass(frozen=True)
class Declaration(Statement):
    pass


@dataclass(frozen=True)
class VariableDecl(Declaration):
    pass


@dataclass(frozen=True)
class LocalDecl(VariableDecl):
    target: Identifier
    type: t.Type


@dataclass(frozen=True)
class InputDecl(VariableDecl):
    target: Identifier
    type: t.Type


@dataclass(frozen=True)
class OutputDecl(VariableDecl):
    target: Identifier
    type: t.Type


@dataclass(frozen=True)
class SharedDecl(VariableDecl):
    target: Identifier
    type: t.Type


@dataclass(frozen=True)
class TypeDecl(Declaration):
    target: Identifier
    type: t.Type


@dataclass(frozen=True)
class InstanceDecl(Declaration):
    target: Identifier
    module: Identifier
    arguments: List[Tuple[Identifier, e.Expression]]


@dataclass(frozen=True)
class HoleStmt(Statement):
    pass
