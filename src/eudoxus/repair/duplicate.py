from typing import Dict, List

import eudoxus.ast.module as m
import eudoxus.ast.statement as s
from eudoxus.ast.node import Node, Position
from eudoxus.repair.interface import Checker


class DuplicateChecker(Checker):
    """
    Remove all duplicate type, variable, instance, and module declarations.
    """

    def check(self, modules: List[m.Module]) -> List[Dict[Position, Node]]:
        rewrites = {}

        for module in modules:
            components = [
                module.instances,
                module.inputs,
                module.outputs,
                module.sharedvars,
                module.locals,
                module.types,
            ]
            for i in range(len(components)):
                component = components[i]
                existing_names = set()
                for j in range(i):
                    other = components[j]
                    for other_component in other.statements:
                        existing_names.add(other_component.target.name)

                component_pos = component.position
                new_decls = []
                for component in component.statements:
                    if component.target.name not in existing_names:
                        existing_names.add(component.target.name)
                        new_decls.append(component)
                rewrites[component_pos] = s.Block(component_pos, new_decls)

        return [rewrites]
