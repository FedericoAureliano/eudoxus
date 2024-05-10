from dataclasses import dataclass
from typing import List

from eudoxus.ast.node import Node


@dataclass(frozen=True)
class Command(Node):
    pass


@dataclass(frozen=True)
class Block(Command):
    commands: List[Command]


@dataclass(frozen=True)
class Induction(Command):
    k: int


@dataclass(frozen=True)
class BoundedModelChecking(Command):
    k: int


@dataclass(frozen=True)
class HoleCmd(Command):
    pass
