from typing import Dict, List

import eudoxus.ast.expression as e
import eudoxus.ast.module as m
import eudoxus.ast.statement as s
import eudoxus.ast.type as t
from eudoxus.analyze.io import IOChecker
from eudoxus.ast.node import HoleId, Identifier, Node, Position
from eudoxus.repair.interface import Checker


class InstanceChecker(Checker):
    """
    Replace `var x: T` with `instance x: T(y:(??))` if T is a module with a
    single input/output y. Replace `instance x: T()` with `instance x: T(y:(??))`.
    """

    def __init__(self):
        self.position = -2000

    def fpos(self):
        self.position -= 1
        return Position(self.position)

    def repair_args(self, moudle_name, modules, existing_args):
        # find the module with the given name
        module = None
        for mod in modules:
            if mod.name.name == moudle_name:
                module = mod
                break
        if module is None:
            return [(HoleId(self.fpos()), e.HoleExpr(self.fpos()))]

        # find the input/output variables of the module
        ios = IOChecker().check(module)

        # make existing_args a dictionary
        existing_args = {k.name: v for k, v in existing_args}

        new_args = []
        for io in sorted(ios):
            if io in existing_args:
                new_args.append((Identifier(self.fpos(), io), existing_args[io]))
            else:
                new_args.append((Identifier(self.fpos(), io), e.HoleExpr(self.fpos())))
        return new_args

    def check(self, modules: List[m.Module]) -> List[Dict[Position, Node]]:
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
                            args = self.repair_args(rhs.name, modules, [])
                            new_instance = s.InstanceDecl(self.fpos(), lhs, rhs, args)
                            new_instances.append(new_instance)
                        else:
                            new_locals.append(decl)
                    case _:
                        new_locals.append(decl)

            for decl in module.instances.statements:
                match decl:
                    case s.InstanceDecl(_, lhs, mod, args):
                        if mod.name in self.declared_modules:
                            new_args = self.repair_args(mod.name, modules, args)
                            new_instance = s.InstanceDecl(
                                self.fpos(), lhs, mod, new_args
                            )
                            new_instances.append(new_instance)
                        else:
                            new_instances.append(decl)
                    case _:
                        new_instances.append(decl)

            ipos = module.instances.position
            rewrites[ipos] = s.Block(self.fpos(), new_instances)

            lpos = module.locals.position
            rewrites[lpos] = s.Block(self.fpos(), new_locals)

        return [rewrites]
