from typing import Dict, List

import eudoxus.ast.module as m
import eudoxus.ast.statement as s
import eudoxus.ast.type as t
from eudoxus.ast.node import Node, Position
from eudoxus.repair.interface import Checker


class CycleChecker(Checker):
    """
    Remove cyclic type declarations.
    """

    def check(self, modules: List[m.Module]) -> List[Dict[Position, Node]]:
        rewrites = {}

        for module in modules:
            graph = {}
            for type in module.types.statements:
                match type:
                    case s.TypeDecl(_, lhs, t.SynonymType(_, rhs)):
                        graph[lhs.name] = rhs.name

            # if there is a cycle, remove the type declarations
            if not graph:
                continue
            start = next(iter(graph))
            cycle = self.find_cycle(start, graph, [])

            new_decls = []
            for type in module.types.statements:
                if type.target.name not in cycle:
                    new_decls.append(type)

            rewrites[module.types.position] = s.Block(module.types.position, new_decls)

        return [rewrites]

    def find_cycle(self, curr: str, graph: Dict[str, str], visited) -> List[str]:
        if curr in visited:
            return visited
        visited.append(curr)
        if curr in graph:
            return self.find_cycle(graph[curr], graph, visited)
        return []
