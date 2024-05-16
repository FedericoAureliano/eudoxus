from typing import List, Tuple

import eudoxus.ast.expression as e
import eudoxus.ast.statement as s
from eudoxus.ast.node import Identifier
from eudoxus.repair.scope import ScopeStack


class SequentialChecker:
    """
    Check if the next block is sequential or parallel.
    """

    def add(self, target: Identifier):
        if self.scopes.exists(target.name):
            self.sequential = True
        self.used_names.add(target.name)
        self.scopes.add(target.name, target.position)

    def enter_scope(self, node):
        match node:
            case s.Block(_, _):
                self.scopes.enter_scope()
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
                self.scopes.exit_scope()

    def check(self, next: s.Block) -> Tuple[bool, List[str]]:
        self.scopes = ScopeStack()

        self.used_names = set()
        self.sequential = False

        next.traverse(self.enter_scope, self.exit_scope)

        return self.sequential, list(self.used_names)
