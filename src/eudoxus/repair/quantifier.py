from typing import Dict, List

import eudoxus.ast.expression as e
import eudoxus.ast.module as m
from eudoxus.ast.node import Identifier, Node, Position
from eudoxus.repair.interface import Checker


class QuantifierChecker(Checker):
    """
    Rename all quantifier variables so that they are unique in each module.
    For example,
    ```
    var x: boolean;
    assert (forall (x1: integer) :: x1 = 0);
    assert (forall (x1: boolean) :: x1);
    ```
    becomes
    ```
    var x: boolean;
    assert (forall (x1: integer) :: x1 = 0);
    assert (forall (x2: boolean) :: x2);
    ```
    """

    def get_new_name(self, name):
        name = name.rstrip("0123456789")
        count = 0
        while f"{name}{count}" in self.used_names:
            count += 1
        new_name = f"{name}{count}"
        self.used_names.add(new_name)
        return new_name

    def enter_quant(self, node):
        match node:
            case e.Forall(_, var, _, _) | e.Exists(_, var, _, _):
                new_name = self.get_new_name(var.name)
                self.map = {var.name: new_name}

            case Identifier(position, name):
                if name in self.map:
                    new_id = Identifier(position, self.map[name])
                    self.rewrites[position] = new_id

    def exit_quant(self, node):
        match node:
            case e.Forall(_, _, _, _) | e.Exists(_, _, _, _):
                self.map = {}

    def check(self, modules: List[m.Module]) -> Dict[Position, Node]:
        self.rewrites = {}
        self.used_names = set()
        self.map = {}

        for module in modules:
            module.traverse(self.enter_quant, self.exit_quant)

        return self.rewrites
