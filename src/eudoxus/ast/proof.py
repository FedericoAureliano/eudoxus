from dataclasses import dataclass

from eudoxus.ast.node import Node


@dataclass(frozen=True)
class Command(Node):
    pass


@dataclass(frozen=True)
class Block(Command):
    commands: list[Command]


@dataclass(frozen=True)
class Induction(Command):
    k: int


@dataclass(frozen=True)
class BoundedModelChecking(Command):
    k: int
