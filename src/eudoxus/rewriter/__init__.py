from typing import Dict

from eudoxus.ast.node import Node, Position


class Rewriter:
    def __init__(self, rules: Dict[Position, Node]):
        self.rules = rules

    def rewrite_node(self, cls, pos, children) -> Node:
        if pos in self.rules:
            return self.rules[pos]
        return cls(pos, *children)

    def rewrite(self, node: Node) -> Node:
        return node.visit(self.rewrite_node)
