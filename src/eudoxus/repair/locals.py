from typing import Dict, List

import eudoxus.ast.module as m
import eudoxus.ast.statement as s
import eudoxus.ast.type as t
from eudoxus.ast.node import Identifier, Node, Position
from eudoxus.repair.interface import Checker


class LocalChecker(Checker):
    """
    Find cases where a type is declared but not used as a type.
    ```
    type x: boolean;
    ...
    assert x;
    ...
    ```
    becomes
    ```
    var x: boolean;
    ...
    assert x;
    ...
    ```
    """

    def __init__(self):
        self.position = -6000

    def fpos(self):
        self.position -= 1
        return Position(self.position)

    def enter_locals(self, node):
        match node:
            case s.TypeDecl(_, _, _) as ty:
                self.declared_types.append(ty)
            case t.SynonymType(_, Identifier(_, target)):
                self.used_types.append(target)

    def exit_locals(self, _):
        pass

    def check(self, modules: List[m.Module]) -> List[Dict[Position, Node]]:
        self.rewrites = {}
        self.declared_types = []
        self.used_types = []

        for module in modules:
            module.traverse(self.enter_locals, self.exit_locals)

            new_decls = []
            for ty in self.declared_types:
                if ty.target.name in self.used_types:
                    new_decls.append(ty)

            type_pos = module.types.position
            new_block = s.Block(self.fpos(), new_decls)
            self.rewrites[type_pos] = new_block

        return [self.rewrites]
