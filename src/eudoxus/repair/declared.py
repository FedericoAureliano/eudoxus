from typing import Dict, List, Tuple

import eudoxus.ast.expression as e
import eudoxus.ast.module as m
import eudoxus.ast.proof as p
import eudoxus.ast.statement as s
import eudoxus.ast.type as t
from eudoxus.ast.node import HoleId, Identifier, Node, Position
from eudoxus.repair.interface import Checker


class DeclaredChecker(Checker):
    """
    Declare types, instances, and modules that are used but not declared.
    """

    def declared_visitor(self, cls, pos, children):
        match cls:
            case s.TypeDecl if isinstance(children[1], t.EnumeratedType):
                self.declared_types.add(children[0].name)
            case s.TypeDecl if isinstance(children[1], t.RecordType):
                self.declared_types.add(children[0].name)
            case s.TypeDecl:
                self.declared_types.add(children[0].name)
            case s.InstanceDecl:
                self.declared_instances.add(children[0].name)

        return cls(pos, *children)

    def used_visitor(self, cls, pos, children):
        match cls:
            case t.SynonymType:
                self.used_types.add(children[0].name)
            case s.InstanceDecl:
                self.used_modules.add(children[1].name)
            case s.Next:
                self.used_instances.add(children[0].name)
            case e.InstanceSelect:
                self.used_instances.add(children[0].name)

        return cls(pos, *children)

    def check(
        self, modules: List[m.Module]
    ) -> Tuple[List[Dict[Position, Node]], List[m.Module]]:
        self.position = -1000

        def new_pos():
            self.position -= 1
            return Position(self.position)

        rewrites = {}

        self.declared_modules = set([m.name.name for m in modules])
        self.used_modules = set()

        for module in modules:
            self.declared_types = set()
            self.declared_instances = set()
            self.used_types = set()
            self.used_instances = set()

            module.visit(self.declared_visitor)
            module.visit(self.used_visitor)

            types_to_declare = self.used_types - self.declared_types
            instances_to_declare = self.used_instances - self.declared_instances

            type_block = module.types
            pt = type_block.position
            new_type_decls = []
            for type_name in sorted(types_to_declare):
                if type_name in self.declared_modules:
                    # don't declare a type with an existing module's name
                    continue
                new_type_decl = s.TypeDecl(
                    new_pos(), Identifier(new_pos(), type_name), t.HoleType(new_pos())
                )
                new_type_decls.append(new_type_decl)
            new_type_block = s.Block(new_pos(), new_type_decls + type_block.statements)
            rewrites[pt] = new_type_block

            instance_block = module.instances
            pi = instance_block.position
            new_instance_decls = []
            for instance_name in sorted(instances_to_declare):
                new_instance_decl = s.InstanceDecl(
                    new_pos(),
                    Identifier(new_pos(), instance_name),
                    HoleId(new_pos()),
                    [],
                )
                new_instance_decls.append(new_instance_decl)
            new_instance_block = s.Block(
                new_pos(), new_instance_decls + instance_block.statements
            )
            rewrites[pi] = new_instance_block

        modules_to_declare = self.used_modules - self.declared_modules
        new_modules = []
        for module_name in modules_to_declare:
            new_module = m.Module(
                new_pos(),
                Identifier(new_pos(), module_name),
                s.Block(new_pos(), []),
                s.Block(new_pos(), []),
                s.Block(new_pos(), []),
                s.Block(new_pos(), []),
                s.Block(new_pos(), []),
                s.Block(new_pos(), []),
                s.Block(new_pos(), []),
                s.Block(new_pos(), []),
                e.BooleanValue(new_pos(), True),
                p.Block(new_pos(), []),
            )
            new_modules.append(new_module)

        return [rewrites], new_modules
