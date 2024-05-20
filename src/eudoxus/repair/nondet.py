from typing import Dict, List

import eudoxus.ast.expression as e
import eudoxus.ast.module as m
import eudoxus.ast.statement as s
from eudoxus.ast.node import Identifier, Node, Position
from eudoxus.repair.interface import Checker


class NondetChecker(Checker):
    """
    Replace every nondet expression with a fresh variable and corresponding declaration.
    """

    def __init__(self) -> None:
        self.rewrites2 = {}
        self.to_declare_stack = []
        self.block_stack = []
        self.new_blocks = {}
        self.count = 0
        self.position = -5000

    def fpos(self):
        self.position += 1
        return Position(self.position)

    def get_name(self):
        self.count += 1
        return f"nondet_{self.count}"

    def nondet_enter(self, node):
        match node:
            case s.Block(pos, _):
                self.to_declare_stack.append(set())
                self.block_stack.append(node)
            case e.Nondet(pos):
                new_id = Identifier(self.fpos(), self.get_name())
                self.to_declare_stack[-1].add(new_id)
                self.rewrites2[pos] = e.FunctionApplication(self.fpos(), new_id, [])

    def nondet_exit(self, node):
        match node:
            case s.Block(_, _):
                to_declare = self.to_declare_stack.pop()

                if len(to_declare) > 0:
                    new_stmts = []
                    for id in sorted(to_declare, key=lambda x: x.name):
                        new_stmts.append(s.Havoc(self.fpos(), id))

                    parent = self.block_stack[0]
                    parent_pos = parent.position
                    if parent_pos not in self.new_blocks:
                        self.new_blocks[parent_pos] = parent.statements
                    self.new_blocks[parent_pos] = (
                        new_stmts + self.new_blocks[parent_pos]
                    )

                self.block_stack.pop()

    def check(self, modules: List[m.Module]) -> List[Dict[Position, Node]]:
        for module in modules:
            module.traverse(self.nondet_enter, self.nondet_exit)

        rewrites1 = {}
        for pos, stmts in self.new_blocks.items():
            rewrites1[pos] = s.Block(pos, stmts)

        return [rewrites1, self.rewrites2]
