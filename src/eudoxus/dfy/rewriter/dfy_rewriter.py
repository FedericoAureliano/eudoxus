from typing import Dict

import eudoxus.ast.expression as e
import eudoxus.ast.statement as s
import eudoxus.ast.type as t
from eudoxus.ast.node import Node, Position
from eudoxus.dfy.ast.module import DfyModule
from eudoxus.dfy.ast.params import Param, Params
from eudoxus.dfy.ast.statement import Ensures, Requires, Return


class DfyRewriter:
    def __init__(self, rules: Dict[Position, Node]):
        self.rules = rules

    def rewrite_node(self, node: Node) -> Node:
        if node.position in self.rules:
            return self.rules[node.position]
        return node

    def rewrite(self, node: Node) -> Node:
        node = self.rewrite_node(node)
        match node:
            case DfyModule(
                position,
                method_or_function,
                name,
                params,
                return_type,
                body,
                requires,
                ensures,
            ):
                new_params = self.rewrite(params)
                new_return_type = self.rewrite(return_type)
                new_body = self.rewrite(body)
                new_requires = [self.rewrite(r) for r in requires]
                new_ensures = [self.rewrite(e) for e in ensures]

                return DfyModule(
                    position,
                    method_or_function,
                    name,
                    new_params,
                    new_return_type,
                    new_body,
                    new_requires,
                    new_ensures,
                )
            case e.Selection(position, target, field):
                new_target = self.rewrite(target)
                new_field = self.rewrite(field)
                return e.Selection(position, new_target, new_field)
            case e.Application(position, function, arguments):
                new_function = self.rewrite(function)
                new_arguments = [self.rewrite(a) for a in arguments]
                return e.Application(position, new_function, new_arguments)
            case e.Array(default):
                new_default = self.rewrite(default)
                return e.Array(new_default)
            case s.Instance(position, name, module, arguments):
                new_name = self.rewrite(name)
                new_module = self.rewrite(module)
                new_arguments = [
                    (self.rewrite(l), self.rewrite(g)) for (l, g) in arguments
                ]
                return s.Instance(position, new_name, new_module, new_arguments)
            case s.Type(position, name, type):
                new_name = self.rewrite(name)
                new_type = self.rewrite(type)
                return s.Type(position, new_name, new_type)
            case s.Constant(position, name, type, value):
                new_name = self.rewrite(name)
                new_type = self.rewrite(type)
                new_value = self.rewrite(value)
                return s.Constant(position, new_name, new_type, new_value)
            case v if isinstance(v, s.Variable):
                vclass = v.__class__
                new_name = self.rewrite(v.target)
                new_type = self.rewrite(v.type)
                return vclass(v.position, new_name, new_type)
            case s.Havoc(position, target):
                new_target = self.rewrite(target)
                return s.Havoc(position, new_target)
            case s.Assume(position, condition):
                new_condition = self.rewrite(condition)
                return s.Assume(position, new_condition)
            case s.Assert(position, condition):
                new_condition = self.rewrite(condition)
                return s.Assert(position, new_condition)
            case Return(position, value):
                new_value = self.rewrite(value)
                return Return(position, new_value)
            case s.Block(position, statements):
                new_statements = [self.rewrite(s) for s in statements]
                return s.Block(position, new_statements)
            case s.If(position, condition, then_branch, else_branch):
                new_condition = self.rewrite(condition)
                new_then_branch = self.rewrite(then_branch)
                new_else_branch = self.rewrite(else_branch)
                return s.If(position, new_condition, new_then_branch, new_else_branch)
            case s.Assignment(position, target, value):
                new_target = self.rewrite(target)
                new_value = self.rewrite(value)
                return s.Assignment(position, new_target, new_value)
            case t.Record(position, fields):
                new_fields = [(self.rewrite(f[0]), self.rewrite(f[1])) for f in fields]
                return t.Record(position, new_fields)
            case t.Enumeration(position, values):
                new_values = [self.rewrite(v) for v in values]
                return t.Enumeration(position, new_values)
            case t.Synonym(position, name):
                new_name = self.rewrite(name)
                return t.Synonym(position, new_name)
            case t.Array(position, index, element):
                new_index = self.rewrite(index)
                new_element = self.rewrite(element)
                return t.Array(position, new_index, new_element)
            case t.Function(position, domain, codomain):
                new_domain = [self.rewrite(d) for d in domain]
                new_codomain = self.rewrite(codomain)
                return t.Function(position, new_domain, new_codomain)
            case Requires(position, condition):
                new_condition = self.rewrite(condition)
                return Requires(position, new_condition)
            case Ensures(position, condition):
                new_condition = self.rewrite(condition)
                return Ensures(position, new_condition)
            case Params(position, params):
                new_params = [self.rewrite(p) for p in params]
                return Params(position, new_params)
            case Param(position, name, type):
                new_name = self.rewrite(name)
                new_type = self.rewrite(type)
                return Param(position, new_name, new_type)

            case _:
                return node
