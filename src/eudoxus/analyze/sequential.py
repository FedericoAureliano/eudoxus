from typing import List, Tuple

import eudoxus.ast.expression as e
import eudoxus.ast.statement as s
from eudoxus.ast.node import Identifier


class SequentialChecker:
    """
    Check if the next block is sequential or parallel.
    """

    def add(self, pos, target: Identifier):
        if pos not in self.pos_to_used:
            self.pos_to_used[pos] = set()
        self.pos_to_used[pos].add(target.name)

    def enter_scope(self, node):
        match node:
            case s.If(pos, _, then_, else_):
                self.edges.append((pos, first(then_)))
                self.edges.append((pos, first(else_)))
            case s.Block(pos, stmts):
                for i in range(len(stmts) - 1):
                    if i == 0:
                        self.edges.append((pos, first(node)))
                    match stmts[i]:
                        case s.If(pos, _, then_, else_):
                            self.edges.append((last(then_), stmts[i + 1].position))
                            self.edges.append((last(else_), stmts[i + 1].position))
                        case _:
                            self.edges.append(
                                (stmts[i].position, stmts[i + 1].position)
                            )
            case s.Havoc(pos, target):
                self.add(pos, target)
            case s.Assignment(pos, e.FunctionApplication(_, target, _), _):
                self.add(pos, target)
            case s.Assignment(
                pos, e.ArraySelect(_, e.FunctionApplication(_, target, _), _), _
            ):
                self.add(pos, target)

    def exit_scope(self, _):
        pass

    def is_sequential(self, pos, used):
        new_used = list(self.pos_to_used.get(pos, set()))
        if duplicates(used + new_used):
            return True

        sequential = False
        for edge in self.edges:
            if edge[0] == pos:
                sequential = sequential or self.is_sequential(edge[1], used + new_used)
        return sequential

    def check(self, next: s.Block) -> Tuple[bool, List[str]]:
        self.pos_to_used = {}
        self.edges = []

        next.traverse(self.enter_scope, self.exit_scope)

        sequential = self.is_sequential(first(next), list())

        used_names = set()
        for used in self.pos_to_used.values():
            used_names.update(used)

        return sequential, list(used_names)


def duplicates(ls):
    return len(ls) != len(set(ls))


def first(b: s.Block):
    if len(b.statements) == 0:
        return b.position
    return b.statements[0].position


def last(b: s.Block):
    if len(b.statements) == 0:
        return b.position
    return b.statements[-1].position
