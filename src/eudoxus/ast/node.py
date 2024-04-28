import dataclasses
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

    def _visit_children(self, visitor):
        children = [getattr(self, v.name) for v in dataclasses.fields(self)]
        new_children = []
        for child in children:
            if isinstance(child, Node):
                new_children.append(child.visit(visitor))
            elif isinstance(child, list):
                new_children.append([c.visit(visitor) for c in child])
            elif isinstance(child, Position):
                continue
            else:
                new_children.append(child)
        return new_children

    def visit(self, visitor):
        """
        Visit the node and its children, calling the visitor on each node.
        param visitor: a function that takes a class, a position, and a list of
                       children, and returns a new node
        """
        new_children = self._visit_children(visitor)
        return visitor(self.__class__, self.position, new_children)


@dataclass(frozen=True)
class Identifier(Node):
    name: str


@dataclass(frozen=True)
class Hole(Node):
    # just in case we try to treat a hole as an identifier
    @property
    def name(self) -> str:
        return "??"
