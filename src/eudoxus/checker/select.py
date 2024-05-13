from typing import Dict, List

import eudoxus.ast.expression as e
import eudoxus.ast.module as m
import eudoxus.ast.statement as s
from eudoxus.ast.node import Identifier, Node, Position
from eudoxus.checker.interface import Checker


class SelectChecker(Checker):
    def declared_visitor(self, cls, pos, children):
        match cls:
            case s.TypeDecl:
                self.declared_types.add(children[0].name)
            case s.LocalDecl | s.OutputDecl | s.InputDecl | s.SharedDecl:
                self.declared_vars.add(children[0].name)

        return cls(pos, *children)

    def selects_visitor(self, cls, pos, children):
        match cls:
            case e.RecordSelect:
                self.selects.append(cls(pos, *children))

        return cls(pos, *children)

    def check(self, modules: List[m.Module]) -> Dict[Position, Node]:
        rewrites = {}

        for module in modules:
            self.declared_types = set()
            self.declared_vars = set()
            self.selects = []
            module.visit(self.declared_visitor)
            module.visit(self.selects_visitor)
            for sel in self.selects:
                match sel:
                    case e.RecordSelect(
                        pos, e.FunctionApplication(_, Identifier(_, n), []), field
                    ):
                        if n not in self.declared_vars and n in self.declared_types:
                            rewrites[pos] = e.EnumValue(pos, field.name)

        return rewrites
