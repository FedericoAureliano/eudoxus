from typing import Dict, List

import eudoxus.ast.expression as e
import eudoxus.ast.module as m
import eudoxus.ast.statement as s
import eudoxus.ast.type as t
from eudoxus.ast.node import Identifier, Node, Position
from eudoxus.checker.interface import Checker


class DeclaredChecker(Checker):
    def declared_visitor(self, cls, pos, children):
        match cls:
            case s.TypeDecl:
                self.declared_types.add(children[0].name)
            case s.LocalDecl | s.OutputDecl | s.InputDecl | s.SharedDecl:
                self.declared_vars.add(children[0].name)

        return cls(pos, *children)

    def used_visitor(self, cls, pos, children):
        match cls:
            case e.FunctionApplication:
                self.used_vars.add(children[0].name)
            case t.SynonymType:
                self.used_types.add(children[0].name)

        return cls(pos, *children)

    def check(self, modules: List[m.Module]) -> Dict[Position, Node]:
        self.position = -1000

        def new_pos():
            self.position += 1
            return Position(self.position)

        rewrites = {}

        for module in modules:
            self.declared_types = set()
            self.used_types = set()
            self.declared_vars = set()
            self.used_vars = set()
            module.visit(self.declared_visitor)
            module.visit(self.used_visitor)

            types_to_declare = self.used_types - self.declared_types
            vars_to_declare = self.used_vars - self.declared_vars

            type_block = module.types
            pt = type_block.position
            new_type_decls = [
                s.TypeDecl(
                    new_pos(), Identifier(new_pos(), name), t.HoleType(new_pos())
                )
                for name in types_to_declare
            ]
            new_type_block = s.Block(new_pos(), new_type_decls + type_block.statements)
            rewrites[pt] = new_type_block

            var_block = module.locals
            pv = var_block.position
            new_var_decls = [
                s.LocalDecl(
                    new_pos(), Identifier(new_pos(), name), t.HoleType(new_pos())
                )
                for name in vars_to_declare
            ]
            new_var_block = s.Block(new_pos(), new_var_decls + var_block.statements)
            rewrites[pv] = new_var_block

        return rewrites
