from dataclasses import dataclass


@dataclass(frozen=True)
class Position:
    unique: int


def pos2str(pos: Position) -> str:
    return str(pos.unique)


def str2pos(s: str) -> Position:
    return Position(int(s))


@dataclass(frozen=True)
class Node:
    position: Position


@dataclass(frozen=True)
class Identifier(Node):
    name: str


@dataclass(frozen=True)
class Hole(Node):
    # just in case we try to treat a hole as an identifier
    @property
    def name(self) -> str:
        return "??"
