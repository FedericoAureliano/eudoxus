from dataclasses import dataclass

from eudoxus.ast.expression import Expression
from eudoxus.ast.node import Node
from eudoxus.ast.proof import Command
from eudoxus.ast.statement import Declaration, Statement


@dataclass(frozen=True)
class Module(Node):
    declarations: list[Declaration]
    init: list[Statement]
    next: list[Statement]
    specification: list[Expression]
    control: list[Command]
