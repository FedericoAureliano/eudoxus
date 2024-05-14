from typing import Dict, List, Tuple

import eudoxus.ast.expression as e
import eudoxus.ast.module as m
import eudoxus.ast.proof as p
import eudoxus.ast.statement as s
from eudoxus.ast.node import Identifier, Node, Position
from eudoxus.checker.interface import Checker


class InstanceChecker(Checker):
    def declared_visitor(self, cls, pos, children):
        match cls:
            case s.InstanceDecl:
                self.used_modules.add(children[1].name)

        return cls(pos, *children)

    def check(
        self, modules: List[m.Module]
    ) -> Tuple[Dict[Position, Node], List[m.Module]]:
        self.position = -2000

        def new_pos():
            self.position += 1
            return Position(self.position)

        rewrites = {}

        self.declared_modules = set()
        self.used_modules = set()

        for module in modules:
            self.declared_modules.add(module.name.name)
            module.visit(self.declared_visitor)

        modules_to_declare = self.used_modules - self.declared_modules
        new_modules = []
        for module_name in modules_to_declare:
            new_module = m.Module(
                new_pos(),
                Identifier(new_pos(), module_name),
                s.Block(new_pos(), []),
                s.Block(new_pos(), []),
                s.Block(new_pos(), []),
                s.Block(new_pos(), []),
                s.Block(new_pos(), []),
                s.Block(new_pos(), []),
                s.Block(new_pos(), []),
                s.Block(new_pos(), []),
                e.BooleanValue(new_pos(), True),
                p.Block(new_pos(), []),
            )
            new_modules.append(new_module)

        return rewrites, new_modules
