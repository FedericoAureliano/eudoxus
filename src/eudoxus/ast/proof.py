from dataclasses import dataclass
from typing import List

from eudoxus.ast.node import Node


@dataclass(frozen=True)
class Command(Node):
    def is_empty(self):
        return False


@dataclass(frozen=True)
class Block(Command):
    commands: List[Command]

    def is_empty(self):
        return len(self.commands) == 0


@dataclass(frozen=True)
class Induction(Command):
    k: int


@dataclass(frozen=True)
class BoundedModelChecking(Command):
    k: int


@dataclass(frozen=True)
class HoleCmd(Command):
    pass
