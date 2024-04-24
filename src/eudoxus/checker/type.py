from typing import Dict, List

import z3
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
        self.term_sort = self.declare_sort("eudoxus.term")
        self.symbol_sort = self.declare_sort("eudoxus.symbol")
        self.type_adt = z3.Datatype("eudoxus.type")
        self.type_adt.declare("boolean")
        self.type_adt.declare("integer")
        self.type_adt.declare("float")
        self.type_adt.declare("bv", ("size", self.term_sort))
        self.type_adt.declare("enum", ("values", z3.SeqSort(self.symbol_sort)))
        self.type_adt.declare(
            "array", ("index", self.type_adt), ("element", self.type_adt)
        )
        self.type_adt = self.type_adt.create()

        self.get_type_expr = self.declare_function(
            "eudoxus.type.get", self.term_sort, self.type_adt
        )

        self.variants = {}
        self.variables = {}
        self.type_synonyms = {}
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
            self.add_soft_constraint(
                self.get_type_expr(spec) == self.type2z3(boolean), pos
            )
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

    def type_from_model(self, model, assigned_type):
        for x, v in self.reverse_type_map.items():
            if model.eval(x == assigned_type):
                return v
        return None

    def repair(self, model, original_node, assigned_term):
        match assigned_term.sort():
            case self.type_adt:
                found = self.type_from_model(model, assigned_term)
                return Hole(original_node.position) if found is None else found
            case self.term_sort:
                found = self.type_from_model(model, self.get_type_expr(assigned_term))
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
                fresh_x = self.declare_function("eudoxus.type." + x, [self.type_sort])
                self.type_instances[x] = (fresh_x, [])

                fresh_y = self.fresh_constant(self.type_sort, "eudoxus.type.")
                correct_y = self.type2z3(y)

                self.add_hard_constraint(fresh_x() == fresh_y)
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
                                self.term_sort, "eudoxus.term." + variant.name + "."
                            )
                            self.variants[variant.name] = new_variant
                        self.add_soft_constraint(
                            self.get_type_expr(new_variant) == self.type2z3(y),
                            variant.position,
                        )

            case s.Variable(_, e.Identifier(_, x), y):
                # Input: var <x>: <y>;
                # Constraints:
                #  - type(fresh_x) == fresh_y (hard)
                #  - fresh_y == correct_y     (soft)
                fresh_x = self.fresh_constant(self.term_sort, "eudoxus.term." + x + ".")
                self.variables[x] = fresh_x

                fresh_y = self.fresh_constant(self.type_adt, "eudoxus.type.")
                correct_y = self.type2z3(y)

                self.add_hard_constraint(self.get_type_expr(fresh_x) == fresh_y)
                self.add_soft_constraint(fresh_y == correct_y, y.position)
                self.to_repair[y.position] = (fresh_y, y)
            case _:
                raise ValueError(f"Unsupported declaration {decl}")

    def stmt2z3(self, stmt: s.Statement) -> None:
        match stmt:
            case s.Assignment(_, x, y):
                # Input: <x> = <y>
                # Constraints:
                #  - type(z3x) == type(z3y)  (hard)
                z3x = self.expr2z3(x)
                z3y = self.expr2z3(y)
                self.add_soft_constraint(
                    self.get_type_expr(z3x) == self.get_type_expr(z3y), y.position
                )
            case s.If(_, x, y, z):
                # Input: if <x> then <y> else <z>
                # Constraints:
                #  - type(z3x) == z3boolean  (hard)
                #  - constraints from y
                #  - constraints from z
                z3x = self.expr2z3(x)
                z3boolean = self.type2z3(boolean)
                self.add_soft_constraint(
                    self.get_type_expr(z3x) == z3boolean, x.position
                )
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
                self.add_soft_constraint(
                    self.get_type_expr(z3x) == z3boolean, x.position
                )
            case _:
                raise ValueError(f"Unsupported statement {stmt}")

    def type2z3(self, type: t.Type) -> ExprRef:
        match type:
            case t.Boolean(_):
                return self.type_adt.boolean
            case t.Integer(_):
                return self.type_adt.integer
            case t.Float(_):
                return self.type_adt.float
            case t.BitVector(_, size):
                size = self.expr2z3(e.Integer(predefined, size))
                return self.type_adt.bv(size)
            case t.Synonym(_, t.Identifier(_, id)):
                out = self.type_synonyms[id]
                self.reverse_type_map[out] = type
                return out
            case t.Array(_, index, value):
                index = self.type2z3(index)
                value = self.type2z3(value)
                return self.type_adt.array(index, value)
            case t.Enumeration(_, values):
                values = [self.fresh_constant(self.symbol_sort, v) for v in values]
                return self.type_adt.enum(z3.Seq(*values))
            case _:
                raise ValueError(f"Unsupported type {type}")

    def expr2z3(self, expr: e.Expression) -> ExprRef:
        def all_equal_types(args):
            a0 = self.expr2z3(args[0])
            for i in range(1, len(args)):
                ai = self.expr2z3(args[i])
                self.add_hard_constraint(
                    self.get_type_expr(ai) == self.get_type_expr(a0)
                )

        def all_some_type(args, ty):
            for i in range(len(args)):
                ai = self.expr2z3(args[i])
                self.add_hard_constraint(self.get_type_expr(ai) == self.type2z3(ty))

        if isinstance(expr, e.Constant) and expr in self.constants:
            return self.constants[expr]

        match expr:
            case e.Boolean(_, c):
                fresh = self.fresh_constant(
                    self.term_sort, "eudoxus.term.boolean." + str(c) + "."
                )
                self.constants[expr] = fresh
                self.add_soft_constraint(
                    self.get_type_expr(fresh) == self.type2z3(boolean), expr.position
                )
                self.to_repair[expr.position] = (fresh, expr)
                return fresh
            case e.Integer(_, c):
                fresh = self.fresh_constant(
                    self.term_sort, "eudoxus.term.integer." + str(c) + "."
                )
                self.constants[expr] = fresh
                expected = self.type2z3(integer)
                self.add_soft_constraint(
                    self.get_type_expr(fresh) == expected, expr.position
                )
                self.to_repair[expr.position] = (fresh, expr)
                return fresh
            case e.BitVector(_, c, width):
                fresh = self.fresh_constant(
                    self.term_sort, "eudoxus.term.bv." + str(c) + "." + str(width) + "."
                )
                self.constants[expr] = fresh
                expected = self.type2z3(t.BitVector(predefined, width))
                self.add_soft_constraint(
                    self.get_type_expr(fresh) == expected, expr.position
                )
                self.to_repair[expr.position] = (fresh, expr)
                return fresh
            case e.Application(_, op, args) if isinstance(op, e.Operator):
                old_variables = self.variables.copy()
                arity = len(args) + 1
                match op:
                    case e.Or(_):
                        name = "eudoxus.term.or"
                        all_some_type(args, boolean)
                    case e.And(_):
                        name = "eudoxus.term.and"
                        all_some_type(args, boolean)
                    case e.Not(_):
                        name = "eudoxus.term.not"
                        all_some_type(args, boolean)
                    case e.Equal(_):
                        name = "eudoxus.term.eq"
                        all_equal_types(args)
                    case e.NotEqual(_):
                        name = "eudoxus.term.neq"
                        all_equal_types(args)
                    case e.LessThan(_):
                        name = "eudoxus.term.lt"
                        all_equal_types(args)
                    case e.GreaterThan(_):
                        name = "eudoxus.term.gt"
                        all_equal_types(args)
                    case e.LessThanOrEqual(_):
                        name = "eudoxus.term.lte"
                        all_equal_types(args)
                    case e.GreaterThanOrEqual(_):
                        name = "eudoxus.term.gte"
                        all_equal_types(args)
                    case e.Add(_):
                        name = "eudoxus.term.add"
                        all_equal_types(args)
                    case e.Subtract(_):
                        name = "eudoxus.term.sub"
                        all_equal_types(args)
                    case e.Multiply(_):
                        name = "eudoxus.term.mul"
                        all_equal_types(args)
                    case e.Divide(_):
                        name = "eudoxus.term.div"
                        all_equal_types(args)
                    case e.Ite(_):
                        name = "eudoxus.term.ite"
                        all_equal_types(args[1:])
                        all_some_type([args[0]], boolean)
                    case e.Quantifier(_, bindings):
                        name = (
                            "eudoxus.term.forall"
                            if isinstance(op, e.Forall)
                            else "eudoxus.term.exists"
                        )
                        for na, ty in bindings:
                            na = na.name
                            self.variables[na] = self.fresh_constant(
                                self.term_sort, "term." + na + "."
                            )
                            self.add_soft_constraint(
                                self.get_type_expr(self.variables[na])
                                == self.type2z3(ty),
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
            case e.Store(_, a, i, v):
                # Input: <a>[<i>] = <v>
                # Constraints:
                #  - type(z3a) == type(eudoxus.store(z3a, z3i, z3v))    (hard)
                #  - type(z3a) == eudoxus.array(type(z3i), type(z3v))   (hard)
                #  - type(z3i) == eudoxus.type.index(z3a)               (hard)
                #  - type(z3v) == eudoxus.element.type(z3a)             (hard)
                z3a = self.expr2z3(a)
                z3i = self.expr2z3(i)
                z3v = self.expr2z3(v)

                name = "eudoxus.term.store"
                arity = 4
                if name not in self.ops:
                    self.ops[name] = self.declare_function(
                        name, [self.term_sort] * arity
                    )
                eudoxus_store = self.ops[name]
                out = eudoxus_store(z3a, z3i, z3v)

                eudoxus_array_t = self.type_adt.array
                eudoxus_index_t = self.type_adt.index
                eudoxus_element_t = self.type_adt.element

                self.add_hard_constraint(
                    self.get_type_expr(z3a) == self.get_type_expr(out)
                )
                self.add_hard_constraint(
                    self.get_type_expr(z3a)
                    == eudoxus_array_t(self.get_type_expr(z3i), self.get_type_expr(z3v))
                )
                self.add_hard_constraint(
                    self.get_type_expr(z3i) == eudoxus_index_t(self.get_type_expr(z3a))
                )
                self.add_hard_constraint(
                    self.get_type_expr(z3v)
                    == eudoxus_element_t(self.get_type_expr(z3a))
                )

                return out

            case e.Index(_, a, i):
                # Input: <a>[<i>]
                # Constraints:
                #  - eudoxus.type.index(type(z3a)) == type(z3i) (hard)
                #  - type(eudoxus.index(a, i)) == eudoxus.element.type(type(z3a)) (hard)
                z3a = self.expr2z3(a)
                z3i = self.expr2z3(i)

                name = "eudoxus.term.index"
                arity = 3
                if name not in self.ops:
                    self.ops[name] = self.declare_function(
                        name, [self.term_sort] * arity
                    )
                eudoxus_index = self.ops[name]
                out = eudoxus_index(z3a, z3i)

                eudoxus_array_t = self.type_adt.array
                eudoxus_index_t = self.type_adt.index
                eudoxus_element_t = self.type_adt.element

                self.add_hard_constraint(
                    eudoxus_index_t(self.get_type_expr(z3a)) == self.get_type_expr(z3i)
                )

                self.add_hard_constraint(
                    self.get_type_expr(out)
                    == eudoxus_element_t(self.get_type_expr(z3a))
                )

                return out
            case _:
                raise ValueError(f"Unsupported expression {expr}")
