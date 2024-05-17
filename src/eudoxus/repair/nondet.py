from typing import Dict, List

import eudoxus.ast.expression as e
import eudoxus.ast.module as m
import eudoxus.ast.statement as s
import eudoxus.ast.type as t
from eudoxus.ast.node import Identifier, Node, Position
from eudoxus.repair.interface import Checker


class NondetChecker(Checker):
    """
    Replace every nondet expression with a fresh variable and corresponding declaration.
    """

    def __init__(self) -> None:
        self.rewrites1 = {}
        self.rewrites2 = {}
        self.stack = []
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
            case s.Block(_, _):
                self.stack.append(set())
            case e.Nondet(pos):
                new_id = Identifier(self.fpos(), self.get_name())
                self.stack[-1].add(new_id)
                self.rewrites2[pos] = e.FunctionApplication(self.fpos(), new_id, [])

    def nondet_exit(self, node):
        match node:
            case s.Block(pos, stmts):
                to_declare = self.stack.pop()
                if to_declare == set():
                    return
                new_stmts = []
                for id in sorted(to_declare, key=lambda x: x.name):
                    new_stmts.append(
                        s.LocalDecl(self.fpos(), id, t.HoleType(self.fpos()))
                    )
                new_stmts.extend(stmts)
                self.rewrites1[pos] = s.Block(self.fpos(), new_stmts)

    def check(self, modules: List[m.Module]) -> List[Dict[Position, Node]]:
        for module in modules:
            module.traverse(self.nondet_enter, self.nondet_exit)

        return [self.rewrites1, self.rewrites2]
