from typing import Dict, List

import eudoxus.ast.module as m
import eudoxus.ast.statement as s
from eudoxus.ast.node import Node, Position
from eudoxus.repair.interface import Checker


class DoubleChecker(Checker):
    """
    Find cases where an id is declared as a type and a var. For example,
    ```
    type x: boolean;
    var x: boolean;
    ```
    becomes
    ```
    var x: boolean;
    ```
    """

    def __init__(self):
        self.position = -6000

    def fpos(self):
        self.position -= 1
        return Position(self.position)

    def enter_double(self, node):
        match node:
            case s.TypeDecl(_, var, _) as ty:
                self.used_types.append(ty)
            case s.LocalDecl(_, var, _):
                self.used_vars.append(var.name)

    def exit_double(self, _):
        pass

    def check(self, modules: List[m.Module]) -> List[Dict[Position, Node]]:
        self.rewrites = {}
        self.used_vars = []
        self.used_types = []

        for module in modules:
            module.traverse(self.enter_double, self.exit_double)

            new_decls = []
            for ty in self.used_types:
                if ty.target.name not in self.used_vars:
                    new_decls.append(ty)

            type_pos = module.types.position
            new_block = s.Block(self.fpos(), new_decls)
            self.rewrites[type_pos] = new_block

        return [self.rewrites]
