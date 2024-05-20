from typing import Dict, List

import eudoxus.ast.module as m
import eudoxus.ast.statement as s
from eudoxus.ast.node import Node, Position
from eudoxus.repair.interface import Checker


class DuplicateChecker(Checker):
    """
    Remoce all duplicate type, variable, instance, and module declarations.
    """

    def check(self, modules: List[m.Module]) -> List[Dict[Position, Node]]:
        rewrites = {}

        for module in modules:
            for component in [
                module.instances,
                module.types,
                module.inputs,
                module.outputs,
                module.sharedvars,
                module.locals,
            ]:
                component_pos = component.position
                component_names = set()
                new_components = []
                for component in component.statements:
                    if component.target.name not in component_names:
                        component_names.add(component.target.name)
                        new_components.append(component)
                rewrites[component_pos] = s.Block(component_pos, new_components)

        return [rewrites]
