from typing import List, Tuple

import eudoxus.ast.expression as e
import eudoxus.ast.statement as s
from eudoxus.ast.node import Identifier


class SequentialChecker:
    """
    Check if the next block is sequential or parallel.
    """

    def add(self, target: Identifier):
        current_block = self.active_blocks[-1]
        if current_block not in self.vars_per_block:
            self.vars_per_block[current_block] = []
        self.vars_per_block[current_block].append(target.name)
        self.used_names.add(target.name)

    def enter_scope(self, node):
        match node:
            case s.Block(pos, _):
                previous_block = self.active_blocks[-1] if self.active_blocks else None
                if previous_block is not None:
                    if previous_block not in self.tree_of_scopes:
                        self.tree_of_scopes[previous_block] = []
                    self.tree_of_scopes[previous_block].append(pos)
                self.active_blocks.append(pos)
            case s.Havoc(_, target):
                self.add(target)
            case s.Assignment(_, e.FunctionApplication(_, target, _), _):
                self.add(target)
            case s.Assignment(
                _, e.ArraySelect(_, e.FunctionApplication(_, target, _), _), _
            ):
                self.add(target)

    def exit_scope(self, node):
        match node:
            case s.Block(_, _):
                self.active_blocks.pop()

    def check(self, next: s.Block) -> Tuple[bool, List[str]]:
        self.vars_per_block = {}
        self.active_blocks = []
        self.tree_of_scopes = {}
        self.used_names = set()

        next.traverse(self.enter_scope, self.exit_scope)

        sequential = dfs(next.position, self.tree_of_scopes, self.vars_per_block, [])

        return sequential, list(self.used_names)


def dfs(bpos, tree_of_scopes, vars_per_block, added_vars):
    vars_in_block = vars_per_block[bpos] if bpos in vars_per_block else []
    vars_in_block += added_vars
    if len(vars_in_block) != len(set(vars_in_block)):
        return True

    children = tree_of_scopes[bpos] if bpos in tree_of_scopes else []
    for child in children:
        if dfs(child, tree_of_scopes, vars_per_block, vars_in_block):
            return True

    return False
