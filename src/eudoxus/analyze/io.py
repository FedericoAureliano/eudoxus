from typing import Set

import eudoxus.ast.statement as s


class IOChecker:
    """
    get the set of I/O variables in a module
    """

    def enter_scope(self, node):
        match node:
            case s.InputDecl(_, target, _):
                self.used_names.add(target.name)
            case s.OutputDecl(_, target, _):
                self.used_names.add(target.name)
            case s.SharedDecl(_, target, _):
                self.used_names.add(target.name)

    def exit_scope(self, _):
        pass

    def check(self, next: s.Block) -> Set[str]:
        self.used_names = set()

        next.traverse(self.enter_scope, self.exit_scope)

        return self.used_names
