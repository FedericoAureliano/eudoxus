from typing import Dict, List

from z3 import ExprRef

import eudoxus.ast.expression as e
import eudoxus.ast.statement as s
import eudoxus.ast.type as t
from eudoxus.ast.module import Module
from eudoxus.ast.node import Hole, Node, Position
from eudoxus.checker.interface import Checker

predefined = Position(0)

boolean = t.Boolean(predefined)
integer = t.Integer(predefined)


class TypeChecker(Checker):
    def __init__(self):
        super().__init__()
        self.type_sort = self.declare_sort("eudoxus.type")
        self.term_sort = self.declare_sort("eudoxus.term")
        self.type = self.declare_function(
            "eudoxus.type", self.term_sort, self.type_sort
        )
        self.types = {}
        self.variants = {}
        self.variables = {}
        self.ops = {}
        self.constants = {}

        # index is position; element is (term, node)
        self.to_repair = {}
        # index is type term, element is node
        self.reverse_type_map = {}

    def check(self, modules: List[Module]) -> Dict[Position, Node]:
        for module in modules:
            for decl in module.types.statements:
                self.decl2z3(decl)
            vars = (
                module.locals.statements
                + module.inputs.statements
                + module.outputs.statements
                + module.sharedvars.statements
            )
            for decl in vars:
                self.decl2z3(decl)
            self.stmt2z3(module.init)
            self.stmt2z3(module.next)
            spec = self.expr2z3(module.specification)
            pos = module.specification.position
            self.add_soft_constraint(self.type(spec) == self.type2z3(boolean), pos)
        positions, model = self.solve()
        holes = {}
        for pos in positions:
            if pos in self.to_repair:
                original_term, original_node = self.to_repair[pos]
                assigned_term = model.eval(original_term, model_completion=True)
                holes[pos] = self.repair(model, original_node, assigned_term)
            else:
                holes[pos] = Hole(pos)
        return holes

    def find_type(self, model, assigned_type):
        for x, v in self.reverse_type_map.items():
            if model.eval(x == assigned_type):
                return v
        return None

    def repair(self, model, original_node, assigned_term):
        match assigned_term.sort():
            case self.type_sort:
                found = self.find_type(model, assigned_term)
                return Hole(original_node.position) if found is None else found
            case self.term_sort:
                found = self.find_type(model, self.type(assigned_term))
                match original_node:
                    case e.Integer(_, v) if isinstance(found, t.BitVector):
                        return e.BitVector(found.position, v, found.width)
                    case e.Integer(_, 0) if isinstance(found, t.Boolean):
                        return e.Boolean(found.position, False)
                    case e.Integer(_, 1) if isinstance(found, t.Boolean):
                        return e.Boolean(found.position, True)
                    case _:
                        return Hole(original_node.position)
            case _:
                return Hole(original_node.position)

    def decl2z3(self, decl: s.Declaration) -> None:
        match decl:
            case s.Type(_, e.Identifier(_, x), y):
                # Input: type <x> = <y>;
                # Constraints:
                #  - fresh_x == fresh_y     (hard)
                #  - fresh_y == correct_y   (soft)
                fresh_x = self.fresh_constant(self.type_sort, "type." + x + ".")
                self.types[x] = fresh_x

                fresh_y = self.fresh_constant(self.type_sort, "type.")
                correct_y = self.type2z3(y)

                self.add_hard_constraint(fresh_x == fresh_y)
                self.add_soft_constraint(fresh_y == correct_y, y.position)
                self.to_repair[y.position] = (fresh_y, y)

                if isinstance(y, t.Enumeration):
                    # If y is an enum, then add constraints to say that
                    # all variants belong to y
                    for variant in y.values:
                        if variant.name in self.variants:
                            new_variant = self.variants[variant.name]
                        else:
                            new_variant = self.fresh_constant(
                                self.term_sort, "term." + variant.name + "."
                            )
                            self.variants[variant.name] = new_variant
                        self.add_soft_constraint(
                            self.type(new_variant) == self.type2z3(y), variant.position
                        )

            case s.Variable(_, e.Identifier(_, x), y):
                # Input: var <x>: <y>;
                # Constraints:
                #  - type(fresh_x) == fresh_y (hard)
                #  - fresh_y == correct_y     (soft)
                fresh_x = self.fresh_constant(self.term_sort, "term." + x + ".")
                self.variables[x] = fresh_x

                fresh_y = self.fresh_constant(self.type_sort, "type.")
                correct_y = self.type2z3(y)

                self.add_hard_constraint(self.type(fresh_x) == fresh_y)
                self.add_soft_constraint(fresh_y == correct_y, y.position)
                self.to_repair[y.position] = (fresh_y, y)
            case _:
                raise ValueError(f"Unsupported declaration {decl}")

    def stmt2z3(self, stmt: s.Statement) -> None:
        match stmt:
            case s.Assignment(_, e.Identifier(_, x), y):
                # Input: <x> = <y>
                # Constraints:
                #  - type(z3x) == type(z3y)  (hard)
                z3x = self.variables[x]
                z3y = self.expr2z3(y)
                self.add_soft_constraint(self.type(z3x) == self.type(z3y), y.position)
            case s.If(_, x, y, z):
                # Input: if <x> then <y> else <z>
                # Constraints:
                #  - type(z3x) == z3boolean  (hard)
                #  - constraints from y
                #  - constraints from z
                z3x = self.expr2z3(x)
                z3boolean = self.type2z3(boolean)
                self.add_soft_constraint(self.type(z3x) == z3boolean, x.position)
                self.stmt2z3(y)
                self.stmt2z3(z)
            case s.Block(_, statements):
                for statement in statements:
                    self.stmt2z3(statement)
            case s.Havoc(_, _):
                return
            case s.Assume(_, x) | s.Assert(_, x):
                # Input: assume/assert x;
                # Constraints:
                #  - type(z3x) == z3boolean  (hard)
                z3x = self.expr2z3(x)
                z3boolean = self.type2z3(boolean)
                self.add_soft_constraint(self.type(z3x) == z3boolean, x.position)
            case _:
                raise ValueError(f"Unsupported statement {stmt}")

    def type2z3(self, type: t.Type) -> ExprRef:
        match type:
            case t.Boolean(_):
                name = "eudoxus.bool"
            case t.Integer(_):
                name = "eudoxus.int"
            case t.Float(_):
                name = "eudoxus.float"
            case t.BitVector(_, size):
                name = f"eudoxus.bv{size}"
            case t.Synonym(_, t.Identifier(_, id)):
                out = self.types[id]
                self.reverse_type_map[out] = type
                return out
            case t.Array(_, index, value):
                index = str(self.type2z3(index))
                value = str(self.type2z3(value))
                name = f"eudoxus.array.{index}.{value}"
            case t.Enumeration(_, values):
                values = [v.name for v in values]
                name = "eudoxus.enum" + ".".join(values)
            case _:
                raise ValueError(f"Unsupported type {type}")

        if name not in self.types:
            self.types[name] = self.declare_constant(name, self.type_sort)

        if "eudoxus" in name:
            self.add_all_diff_hard([v for k, v in self.types.items() if "eudoxus" in k])

        out = self.types[name]
        self.reverse_type_map[out] = type
        return out

    def expr2z3(self, expr: e.Expression) -> ExprRef:
        def all_equal_types(args):
            a0 = self.expr2z3(args[0])
            for i in range(1, len(args)):
                ai = self.expr2z3(args[i])
                self.add_hard_constraint(self.type(ai) == self.type(a0))

        def all_some_type(args, ty):
            for i in range(len(args)):
                ai = self.expr2z3(args[i])
                self.add_hard_constraint(self.type(ai) == self.type2z3(ty))

        if isinstance(expr, e.Constant) and expr in self.constants:
            return self.constants[expr]

        match expr:
            case e.Boolean(_, c):
                fresh = self.fresh_constant(
                    self.term_sort, "term.boolean." + str(c) + "."
                )
                self.constants[expr] = fresh
                self.add_soft_constraint(
                    self.type(fresh) == self.type2z3(boolean), expr.position
                )
                self.to_repair[expr.position] = (fresh, expr)
                return fresh
            case e.Integer(_, c):
                fresh = self.fresh_constant(
                    self.term_sort, "term.integer." + str(c) + "."
                )
                self.constants[expr] = fresh
                expected = self.type2z3(integer)
                self.add_soft_constraint(self.type(fresh) == expected, expr.position)
                self.to_repair[expr.position] = (fresh, expr)
                return fresh
            case e.BitVector(_, c, width):
                fresh = self.fresh_constant(
                    self.term_sort, "term.bv." + str(c) + "." + str(width) + "."
                )
                self.constants[expr] = fresh
                expected = self.type2z3(t.BitVector(predefined, width))
                self.add_soft_constraint(self.type(fresh) == expected, expr.position)
                self.to_repair[expr.position] = (fresh, expr)
                return fresh
            case e.Application(_, op, args) if isinstance(op, e.Operator):
                old_variables = self.variables.copy()
                arity = len(args) + 1
                match op:
                    case e.Or(_):
                        name = "eudoxus.or"
                        all_some_type(args, boolean)
                    case e.And(_):
                        name = "eudoxus.and"
                        all_some_type(args, boolean)
                    case e.Not(_):
                        name = "eudoxus.not"
                        all_some_type(args, boolean)
                    case e.Equal(_):
                        name = "eudoxus.eq"
                        all_equal_types(args)
                    case e.NotEqual(_):
                        name = "eudoxus.neq"
                        all_equal_types(args)
                    case e.LessThan(_):
                        name = "eudoxus.lt"
                        all_equal_types(args)
                    case e.GreaterThan(_):
                        name = "eudoxus.gt"
                        all_equal_types(args)
                    case e.LessThanOrEqual(_):
                        name = "eudoxus.lte"
                        all_equal_types(args)
                    case e.GreaterThanOrEqual(_):
                        name = "eudoxus.gte"
                        all_equal_types(args)
                    case e.Add(_):
                        name = "eudoxus.add"
                        all_equal_types(args)
                    case e.Subtract(_):
                        name = "eudoxus.sub"
                        all_equal_types(args)
                    case e.Multiply(_):
                        name = "eudoxus.mul"
                        all_equal_types(args)
                    case e.Divide(_):
                        name = "eudoxus.div"
                        all_equal_types(args)
                    case e.Quantifier(_, bindings):
                        name = (
                            "eudoxus.forall"
                            if isinstance(op, e.Forall)
                            else "eudoxus.exists"
                        )
                        for na, ty in bindings:
                            na = na.name
                            self.variables[na] = self.fresh_constant(
                                self.term_sort, "term." + na + "."
                            )
                            self.add_soft_constraint(
                                self.type(self.variables[na]) == self.type2z3(ty),
                                ty.position,
                            )
                        all_some_type(args, boolean)
                    case _:
                        raise ValueError(f"Unsupported operator {op}")

                name = name + str(arity - 1)
                if name not in self.ops:
                    self.ops[name] = self.declare_function(
                        name, [self.term_sort] * arity
                    )

                f = self.ops[name]
                args = [self.expr2z3(arg) for arg in args]
                self.variables = old_variables
                return f(*args)
            case e.Application(_, e.Identifier(_, name), []):
                return self.variables[name]
            case e.Variant(_, name):
                return self.variants[name]
            case _:
                raise ValueError(f"Unsupported expression {expr}")
