from typing import Dict, List

import eudoxus.ast.expression as e
import eudoxus.ast.module as m
import eudoxus.ast.statement as s
import eudoxus.ast.type as t
from eudoxus.ast.node import HoleId, Identifier, Node, Position
from eudoxus.checker.interface import Checker


class InstanceChecker(Checker):
    """
    Replace `var x: T` with `instance x: T(??: ??)` if T is a module.
    """

    def check(self, modules: List[m.Module]) -> Dict[Position, Node]:
        self.position = -3000

        def new_pos():
            self.position -= 1
            return Position(self.position)

        rewrites = {}

        self.declared_modules = set([m.name.name for m in modules])

        for module in modules:
            new_instances = []
            new_locals = []
            for decl in module.locals.statements:
                match decl:
                    case s.LocalDecl(_, lhs, t.SynonymType(_, rhs)):
                        if rhs.name in self.declared_modules and isinstance(
                            lhs, Identifier
                        ):
                            args = [(HoleId(new_pos()), e.HoleExpr(new_pos()))]
                            new_instance = s.InstanceDecl(new_pos(), lhs, rhs, args)
                            new_instances.append(new_instance)
                        else:
                            new_locals.append(decl)
                    case _:
                        new_locals.append(decl)

            ipos = module.instances.position
            new_instances = module.instances.statements + new_instances
            rewrites[ipos] = s.Block(new_pos(), new_instances)

            lpos = module.locals.position
            rewrites[lpos] = s.Block(new_pos(), new_locals)

        return rewrites
