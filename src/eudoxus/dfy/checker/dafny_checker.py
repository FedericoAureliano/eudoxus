from typing import Dict, List, Optional

from z3 import BoolSort, ExprRef

import eudoxus.ast.expression as e
import eudoxus.ast.statement as s
import eudoxus.ast.type as t
from eudoxus.ast.module import Module
from eudoxus.ast.node import Hole, Node, Position
from eudoxus.checker.interface import Checker
from eudoxus.dfy.ast import statement as dfy_s
from eudoxus.dfy.ast.expression import Ite, Slice, Subscript
from eudoxus.dfy.ast.list import List as ListType
from eudoxus.dfy.ast.params import Params

predefined = Position(0)

boolean = t.Boolean(predefined)
integer = t.Integer(predefined)


class DfyTypeChecker(Checker):
    def __init__(self, src: Optional[str]) -> None:
        super().__init__()
        self.type_sort = self.declare_sort("eudoxus.type")
        self.term_sort = self.declare_sort("eudoxus.term")
        self.type = self.declare_function(
            "eudoxus.type", self.term_sort, self.type_sort
        )  # maps terms to types
        self.elt_type = self.declare_function(
            "eudoxus.elt_ty", self.type_sort, self.type_sort
        )  # maps list types to element types
        self.is_list = self.declare_function(
            "eudoxus.is_list", self.type_sort, BoolSort()
        )
        self.types = {}
        self.variants = {}
        self.variables = {}
        self.ops = {}
        self.constants = {}

        self.function_symbol_table = {}
        # In theory, we might want to have inference across functions/methods

        # index is position; element is (term, node)
        self.to_repair = {}
        # index is type term, element is node
        self.reverse_type_map = {}

        self.input_holes = []

        self.text = lambda start, end: src[start:end].decode("utf-8")

    def params2z3(self, params: Params) -> None:
        for param in params.params:
            ty, name = param.type, param.name

            self.decl2z3(s.Variable(None, name, ty))

    def check(self, modules: List[Module]) -> Dict[Position, Node]:
        for module in modules:
            self.decl2z3(
                s.Variable(None, e.Identifier(None, "result"), module.return_type)
            )
            self.params2z3(module.params)
            for stmt in module.requires:
                self.stmt2z3(stmt)
            for stmt in module.ensures:
                self.stmt2z3(stmt)

            # add self to symbol table
            self.function_symbol_table[module.name.name] = {
                "params": module.params,
                "return_type": module.return_type,
            }
            if module.method_or_function == "method":
                for stmt in module.body.statements:
                    if isinstance(stmt, dfy_s.Return):
                        value = self.expr2z3(stmt.expr)
                        pos = stmt.position
                        self.add_soft_constraint(
                            self.type(value) == self.type(self.variables["result"]), pos
                        )
                    else:
                        self.stmt2z3(stmt)
            elif module.method_or_function == "function":
                self.expr2z3(module.body)
            else:
                raise ValueError(f"Unsupported module type {module.method_or_function}")

        positions, model = self.solve()

        positions = positions + self.input_holes

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
                self.add_hard_constraint(self.type(fresh_x) == fresh_y)

                if not isinstance(y, Hole):
                    # drop a constraint if not constrained
                    correct_y = self.type2z3(y)
                    self.add_soft_constraint(fresh_y == correct_y, y.position)
                else:
                    self.input_holes.append(y.position)

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
            case s.Assume(_, x) | s.Assert(_, x) | dfy_s.Requires(_, x) | dfy_s.Ensures(
                _, x
            ):
                # Input: assume/assert x;
                # Constraints:
                #  - type(z3x) == z3boolean  (hard)
                z3x = self.expr2z3(x)
                z3boolean = self.type2z3(boolean)
                self.add_soft_constraint(self.type(z3x) == z3boolean, x.position)
            case dfy_s.While(_, cond, inv, dec, body):
                # Input: while <cond> invariant <inv> decreases <dec> { <body> }
                # Constraints:
                #  - type(z3cond) == z3boolean  (hard)
                z3x = self.expr2z3(cond)
                z3boolean = self.type2z3(boolean)
                self.add_soft_constraint(self.type(z3x) == z3boolean, cond.position)
                for i in inv:
                    self.stmt2z3(i)
                for d in dec:
                    self.stmt2z3(d)
                self.stmt2z3(body)
            case dfy_s.Invariant(_, x):
                # Input: invariant x;
                # Constraints:
                #  - type(z3x) == z3boolean  (hard)
                z3x = self.expr2z3(x)
                z3boolean = self.type2z3(boolean)
                self.add_soft_constraint(self.type(z3x) == z3boolean, x.position)
            case dfy_s.Decreases(_, x):
                # Input: decreases x;
                # Constraints:
                #  - type(z3x) == z3int  (hard)
                z3x = self.expr2z3(x)
                z3int = self.type2z3(integer)
                self.add_soft_constraint(self.type(z3x) == z3int, x.position)
            case dfy_s.Comment(_, _):
                return
            case _:
                raise ValueError(f"Unsupported statement {stmt}")

    def type2z3(self, type: t.Type) -> ExprRef:
        """
        Updates the self.types with the introduced type and asserts disinctness of types
        Assigns list_type with the elt_type command
        """
        elt_ty = None
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
            case ListType(_, ty):
                elt_ty = self.type2z3(ty)
                ty_name = str(elt_ty).replace("eudoxus.", "")
                name = f"eudoxus.list.{ty_name}"

            case t.Enumeration(_, values):
                values = [v.name for v in values]
                name = "eudoxus.enum" + ".".join(values)
            case _:
                raise ValueError(f"Unsupported type {type}")

        if name not in self.types:
            self.types[name] = self.declare_constant(name, self.type_sort)
            if elt_ty is not None:
                self.add_hard_constraint(self.elt_type(self.types[name]) == elt_ty)
                self.add_hard_constraint(
                    self.is_list(self.types[name]) == True  # noqa: E712
                )
            else:
                self.add_hard_constraint(
                    self.is_list(self.types[name]) == False  # noqa: E712
                )

        if "eudoxus" in name:
            self.add_all_diff_hard([v for k, v in self.types.items() if "eudoxus" in k])

        out = self.types[name]
        self.reverse_type_map[out] = type
        return out

    def expr2z3(self, expr: e.Expression) -> ExprRef:
        full_expr_type = None

        def all_equal_types(args):
            a0 = self.expr2z3(args[0])
            for i in range(1, len(args)):
                ai = self.expr2z3(args[i])
                self.add_hard_constraint(self.type(ai) == self.type(a0))
            return a0

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
                        full_expr_type = self.type2z3(boolean)
                    case e.And(_):
                        name = "eudoxus.and"
                        all_some_type(args, boolean)
                        full_expr_type = self.type2z3(boolean)

                    case e.Not(_):
                        name = "eudoxus.not"
                        all_some_type(args, boolean)
                        full_expr_type = self.type2z3(boolean)

                    case e.Equal(_):
                        name = "eudoxus.eq"
                        all_equal_types(args)
                        full_expr_type = self.type2z3(boolean)
                    case e.NotEqual(_):
                        name = "eudoxus.neq"
                        all_equal_types(args)
                        full_expr_type = self.type2z3(boolean)
                    case e.LessThan(_):
                        name = "eudoxus.lt"
                        all_equal_types(args)
                        full_expr_type = self.type2z3(boolean)
                    case e.GreaterThan(_):
                        name = "eudoxus.gt"
                        all_equal_types(args)
                        full_expr_type = self.type2z3(boolean)
                    case e.LessThanOrEqual(_):
                        name = "eudoxus.lte"
                        all_equal_types(args)
                        full_expr_type = self.type2z3(boolean)
                    case e.GreaterThanOrEqual(_):
                        name = "eudoxus.gte"
                        all_equal_types(args)
                        full_expr_type = self.type2z3(boolean)
                    case e.Add(_):
                        name = "eudoxus.add"
                        a0 = all_equal_types(args)

                        full_expr_type = self.type(a0)
                    case e.Subtract(_):
                        name = "eudoxus.sub"
                        a0 = all_equal_types(args)
                        full_expr_type = self.type(a0)
                    case e.Multiply(_):
                        name = "eudoxus.mul"
                        a0 = all_equal_types(args)
                        full_expr_type = self.type(a0)
                    case e.Divide(_):
                        name = "eudoxus.div"
                        a0 = all_equal_types(args)
                        full_expr_type = self.type(a0)
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
                full_expr = f(*args)
                if full_expr_type is not None:
                    self.add_soft_constraint(
                        self.type(full_expr) == full_expr_type, expr.position
                    )
                return f(*args)
            case e.Application(_, e.Identifier(_, name), []):
                return self.variables[name]
            case e.Application(_, e.Identifier(_, name), args):
                # this case we're actually calling a function
                if name == "len":
                    # Input: len(<args>)
                    # Constraints:
                    #  - type(z3args) == list_type  (hard)
                    #  - type(z3ret) == z3int       (hard)
                    z3args = self.expr2z3(args[0])
                    z3ret = self.fresh_constant(self.term_sort, "term.")
                    self.add_soft_constraint(
                        self.is_list(self.type(z3args)), args[0].position
                    )
                    self.add_soft_constraint(
                        self.type(z3ret) == self.type2z3(integer), expr.position
                    )
                    return z3ret
                elif name in self.function_symbol_table.keys():
                    if len(args) != len(
                        self.function_symbol_table[name]["params"].params
                    ):
                        # TODO: make this silent by injecting holes.
                        raise ValueError(
                            f"Function {name} called with wrong number of arguments"
                        )

                    for arg, param in zip(
                        args, self.function_symbol_table[name]["params"].params
                    ):
                        self.add_soft_constraint(
                            self.type(self.expr2z3(arg)) == self.type2z3(param.type),
                            arg.position,
                        )
                    z3ret = self.fresh_constant(self.term_sort, "term.")
                    self.add_soft_constraint(
                        self.type(z3ret)
                        == self.type2z3(
                            self.function_symbol_table[name]["return_type"]
                        ),
                        expr.position,
                    )
                    return z3ret

                else:
                    raise ValueError(f"Unsupported function {name}")

            case e.Variant(_, name):
                return self.variants[name]
            case Subscript(_, lst, index):
                # Input: <lst>[<index>]
                # Constraints:
                #  - type(z3index) == z3int
                #  - type(z3ret) == elt_type(z3lst)
                # need is_list(z3lst) to reject indexing into non_list
                z3lst = self.expr2z3(lst)
                self.add_soft_constraint(self.is_list(self.type(z3lst)), lst.position)
                if isinstance(index, Slice):
                    if index.start is not None:
                        z3start = self.expr2z3(index.start)
                        self.add_soft_constraint(
                            self.type(z3start) == self.type2z3(integer),
                            index.start.position,
                        )
                    if index.end is not None:
                        z3end = self.expr2z3(index.end)
                        self.add_soft_constraint(
                            self.type(z3end) == self.type2z3(integer),
                            index.end.position,
                        )
                    if index.step is not None:
                        z3step = self.expr2z3(index.step)
                        self.add_soft_constraint(
                            self.type(z3step) == self.type2z3(integer),
                            index.step.position,
                        )

                    z3ret = self.fresh_constant(self.term_sort, "term.")
                    self.add_soft_constraint(
                        self.type(z3ret) == self.type(z3lst), expr.position
                    )
                else:
                    z3index = self.expr2z3(index)
                    self.add_soft_constraint(
                        self.type(z3index) == self.type2z3(integer), index.position
                    )

                    z3ret = self.fresh_constant(self.term_sort, "term.")
                    self.add_soft_constraint(
                        self.type(z3ret) == self.elt_type(self.type(z3lst)),
                        expr.position,
                    )

                return z3ret
            case Ite(_, cond, then_expr, else_expr):
                # Input: <then_expr> if <cond> else <else_expr>
                # Constraints:
                #  - type(z3cond) == z3boolean
                #  - type(z3then_expr) == type(z3else_expr)
                #  - type(z3ret) == type(z3then_expr)
                z3cond = self.expr2z3(cond)
                z3boolean = self.type2z3(boolean)
                self.add_soft_constraint(self.type(z3cond) == z3boolean, cond.position)

                z3ret = self.fresh_constant(self.term_sort, "term.")
                z3then_expr = self.expr2z3(then_expr)
                z3else_expr = self.expr2z3(else_expr)
                self.add_soft_constraint(
                    self.type(z3then_expr) == self.type(z3else_expr), then_expr.position
                )
                self.add_soft_constraint(
                    self.type(z3ret) == self.type(z3then_expr), expr.position
                )
                return z3ret

            case _:
                raise ValueError(f"Unsupported expression {expr}")
