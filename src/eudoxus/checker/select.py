from typing import Dict, List

import eudoxus.ast.expression as e
import eudoxus.ast.module as m
import eudoxus.ast.statement as s
import eudoxus.ast.type as t
from eudoxus.ast.node import HoleId, Node, Position
from eudoxus.checker.interface import Checker


class SelectChecker(Checker):
    """
    Replace `x.f` with `x` if `f` is a variant of an enum.
    Leave `x.f` as `x.f` if `f` is a field of a record.
    Replace `x.f` with `x.f` (but for instances) if `x` is an instance.
    """

    def declared_visitor(self, cls, pos, children):
        match cls:
            case s.TypeDecl if isinstance(children[1], t.EnumeratedType):
                self.declared_variants.update([v.name for v in children[1].values])
                self.declared_enums.add(children[0].name)
            case s.TypeDecl if isinstance(children[1], t.RecordType):
                self.declared_fields.update([f[0].name for f in children[1].fields])
                self.declared_records.add(children[0].name)
            case s.InstanceDecl:
                self.declared_instances.add(children[0].name)

        return cls(pos, *children)

    def selects_visitor(self, cls, pos, children):
        match cls:
            case e.RecordSelect:
                self.selects.append(cls(pos, *children))

        return cls(pos, *children)

    def check(self, modules: List[m.Module]) -> Dict[Position, Node]:
        rewrites = {}

        for module in modules:
            self.declared_instances = set()
            self.declared_variants = set()
            self.declared_fields = set()
            self.declared_enums = set()
            self.declared_records = set()

            self.selects = []

            module.visit(self.declared_visitor)
            module.visit(self.selects_visitor)

            for sel in self.selects:
                match sel:
                    case e.RecordSelect(pos, e.FunctionApplication(_, n, _), f):
                        if (
                            f.name in self.declared_variants
                            and n.name in self.declared_enums
                        ):
                            rewrites[pos] = e.EnumValue(pos, f.name)
                        elif (
                            f.name in self.declared_fields
                            and n.name in self.declared_records
                        ):
                            continue
                        elif n.name in self.declared_instances:
                            rewrites[pos] = e.InstanceSelect(pos, n, f)
                        elif n.name in self.declared_records:
                            rewrites[f.position] = HoleId(pos)

        return rewrites
