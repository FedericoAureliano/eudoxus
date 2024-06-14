from typing import Dict, List, Optional

from z3 import BoolSort, ExprRef

import eudoxus.ast.expression as e
import eudoxus.ast.statement as s
import eudoxus.ast.type as t
from eudoxus.ast.module import Module
from eudoxus.ast.node import Hole, Node, Position
from eudoxus.dfy.ast import expression as dfy_e
from eudoxus.dfy.ast import statement as dfy_s
from eudoxus.dfy.ast.built_in import built_in_src
from eudoxus.dfy.ast.list_and_sets import ListType, SetType
from eudoxus.dfy.ast.params import Params
from eudoxus.dfy.ast.string import StringType
from eudoxus.dfy.checker.z3opt_interface import Checker

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

        self.has_len = self.declare_function(
            "eudoxus.has_len", self.type_sort, BoolSort()
        )  # just means you can take len of this and check if _ in it

        self.is_list = self.declare_function(
            "eudoxus.is_list", self.type_sort, BoolSort()
        )
        self.types = {}
        self.variants = {}
        self.variables = {}
        self.ops = {}
        self.constants = {}
        self.terms = {}

        self.function_symbol_table = {}
        # In theory, we might want to have inference across functions/methods

        # index is position; element is (term, node)
        self.to_repair = {}
        # index is type term, element is node
        self.reverse_type_map = {}

        self.input_holes = []
        self.src = src

    def reason_to_weight(self, reason: str) -> int:
        match reason:
            case "hole":
                return 0
            case "bad_constant":
                return 1
            case "bad_type":
                return 5
            case other if other.startswith("bad_expr_"):
                depth = int(other.split("_")[2])
                return 10 + depth ^ 2
            case "hard":
                return 5000
            case "default":
                return 1
        raise NotImplementedError(f"Unsupported reason {reason}")

    def text(self, start, end):
        def offset(x, inc):
            return x - inc * 1000

        if start >= 0:
            return self.src[start:end].decode("utf-8")
        else:
            builtin_idx = start // 1000
            if builtin_idx in built_in_src.keys():
                return built_in_src[builtin_idx][
                    offset(start, builtin_idx) : offset(end, builtin_idx)
                ]

    def params2z3(self, params: Params) -> None:
        for param in params.params:
            ty, name = param.type, param.name

            self.decl2z3(s.Variable(None, name, ty))

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

                self.add_soft_constraint(fresh_x == fresh_y, decl.position, "hard")
                self.add_soft_constraint(fresh_y == correct_y, y.position, "bad_type")
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
                            self.type(new_variant) == self.type2z3(y),
                            variant.position,
                            "bad_type",
                        )

            case s.Variable(_, e.Identifier(_, x), y):
                # Input: var <x>: <y>;
                # Constraints:
                #  - type(fresh_x) == fresh_y (hard)
                #  - fresh_y == correct_y     (soft)
                fresh_x = self.fresh_constant(self.term_sort, "term." + x + ".")

                self.variables[x] = fresh_x
                fresh_y = self.fresh_constant(self.type_sort, "type.")
                self.add_soft_constraint(
                    self.type(fresh_x) == fresh_y, decl.position, "hard"
                )

                if not isinstance(y, Hole):
                    # drop a constraint if not constrained
                    correct_y = self.type2z3(y)
                    self.add_soft_constraint(
                        fresh_y == correct_y, y.position, "bad_type"
                    )
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
                depth = self.get_depth(z3x)
                self.add_soft_constraint(
                    self.type(z3x) == self.type(z3y), y.position, f"bad_expr_{depth}"
                )
            case dfy_s.DeclAssignment(_, x, y, ty_hole):
                # Input: <x> = <y>
                # Constraints:
                #  - type(z3x) == type(z3y)  (hard)

                self.decl2z3(s.Variable(None, x, ty_hole))
                z3x = self.variables[x.name]
                z3y = self.expr2z3(y)
                depth = self.get_depth(z3y)
                self.add_soft_constraint(
                    self.type(z3x) == self.type(z3y), y.position, f"bad_expr_{depth}"
                )
            case s.If(_, x, y, z):
                # Input: if <x> then <y> else <z>
                # Constraints:
                #  - type(z3x) == z3boolean  (hard)
                #  - constraints from y
                #  - constraints from z
                z3x = self.expr2z3(x)
                z3boolean = self.type2z3(boolean)
                depth = self.get_depth(z3x)
                self.add_soft_constraint(
                    self.type(z3x) == z3boolean, x.position, f"bad_expr_{depth}"
                )
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
                depth = self.get_depth(z3x)
                self.add_soft_constraint(
                    self.type(z3x) == z3boolean, x.position, f"bad_expr_{depth}"
                )
            case dfy_s.While(_, cond, inv, dec, body):
                # Input: while <cond> invariant <inv> decreases <dec> { <body> }
                # Constraints:
                #  - type(z3cond) == z3boolean  (hard)
                z3x = self.expr2z3(cond)
                z3boolean = self.type2z3(boolean)
                depth = self.get_depth(z3x)
                self.add_soft_constraint(
                    self.type(z3x) == z3boolean, cond.position, f"bad_expr_{depth}"
                )
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
                depth = self.get_depth(z3x)
                self.add_soft_constraint(
                    self.type(z3x) == z3boolean, x.position, f"bad_expr_{depth}"
                )
            case dfy_s.Decreases(_, x):
                # Input: decreases x;
                # Constraints:
                #  - type(z3x) == z3int  (hard)
                z3x = self.expr2z3(x)
                z3int = self.type2z3(integer)
                depth = self.get_depth(z3x)
                self.add_soft_constraint(
                    self.type(z3x) == z3int, x.position, f"bad_expr_{depth}"
                )
            case dfy_s.Comment(_, _):
                return
            case dfy_s.Append(_, lst, item):
                # Input: <lst>.append(<item>)
                # Constraints:
                #  - type(z3lst) == list_type  (hard)
                #  - type(z3item) == elt_type(z3lst)  (hard)
                z3lst = self.expr2z3(lst)
                z3item = self.expr2z3(item)
                self.add_soft_constraint(self.is_list(self.type(z3lst)), lst.position)
                self.add_soft_constraint(
                    self.elt_type(self.type(z3lst)) == self.type(z3item), item.position
                )
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
            case StringType(_):
                name = "eudoxus.string"
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
            case SetType(_, ty):
                elt_ty = self.type2z3(ty)
                ty_name = str(elt_ty).replace("eudoxus.", "")
                name = f"eudoxus.set.{ty_name}"

            case t.Enumeration(_, values):
                values = [v.name for v in values]
                name = "eudoxus.enum" + ".".join(values)
            case _:
                raise ValueError(f"Unsupported type {type}")

        if name not in self.types:
            # First time instantiating
            self.types[name] = self.declare_constant(name, self.type_sort)
            if elt_ty is not None:
                self.add_soft_constraint(
                    self.elt_type(self.types[name]) == elt_ty, type.position, "hard"
                )
            if name.startswith("eudoxus.list"):
                self.add_soft_constraint(
                    self.is_list(self.types[name]) == True,  # noqa: E712
                    type.position,
                    "hard",
                )

                self.add_soft_constraint(
                    self.has_len(self.types[name]) == True,  # noqa: E712
                    type.position,
                    "hard",
                )

            elif name.startswith("eudoxus.set"):
                self.add_soft_constraint(
                    self.has_len(self.types[name]) == True,  # noqa: E712
                    type.position,
                    "hard",
                )
                self.add_soft_constraint(
                    self.is_list(self.types[name]) == False,  # noqa: E712
                    type.position,
                    "hard",
                )
            elif name.startswith("eudoxus.string"):
                self.add_soft_constraint(
                    self.has_len(self.types[name]) == True,  # noqa: E712
                    type.position,
                    "hard",
                )
                self.add_soft_constraint(
                    self.is_list(self.types[name]) == True,  # noqa: E712
                    type.position,
                    "hard",
                )

            else:
                self.add_soft_constraint(
                    self.is_list(self.types[name]) == False,  # noqa: E712
                    type.position,
                    "hard",
                )

        if "eudoxus" in name:
            self.add_all_diff_hard(
                [v for k, v in self.types.items() if "eudoxus" in k],
                position=type.position,
            )

        out = self.types[name]
        self.reverse_type_map[out] = type
        return out

    def expr2z3(self, expr: e.Expression) -> ExprRef:
        full_expr_type = None

        def all_equal_types(args):
            a0 = self.expr2z3(args[0])
            for i in range(1, len(args)):
                ai = self.expr2z3(args[i])
                self.add_soft_constraint(
                    self.type(ai) == self.type(a0), expr.position, "hard"
                )
            return a0

        def all_some_type(args, ty):
            for i in range(len(args)):
                ai = self.expr2z3(args[i])
                self.add_soft_constraint(
                    self.type(ai) == self.type2z3(ty), expr.position, "hard"
                )

        if isinstance(expr, e.Constant) and expr in self.constants:
            return self.constants[expr]

        match expr:
            case e.Identifier(_, name):
                return self.variables[name]
            case e.Boolean(_, c):
                fresh = self.fresh_constant(
                    self.term_sort, "term.boolean." + str(c) + "."
                )
                self.constants[expr] = fresh
                self.add_soft_constraint(
                    self.type(fresh) == self.type2z3(boolean),
                    expr.position,
                    "bad_constant",
                )
                self.to_repair[expr.position] = (fresh, expr)
                return fresh
            case e.Integer(_, c):
                fresh = self.fresh_constant(
                    self.term_sort, "term.integer." + str(c) + "."
                )
                self.constants[expr] = fresh
                expected = self.type2z3(integer)
                self.add_soft_constraint(
                    self.type(fresh) == expected, expr.position, "bad_constant"
                )
                self.to_repair[expr.position] = (fresh, expr)
                return fresh
            case e.BitVector(_, c, width):
                fresh = self.fresh_constant(
                    self.term_sort, "term.bv." + str(c) + "." + str(width) + "."
                )
                self.constants[expr] = fresh
                expected = self.type2z3(t.BitVector(predefined, width))
                self.add_soft_constraint(
                    self.type(fresh) == expected, expr.position, "bad_constant"
                )
                self.to_repair[expr.position] = (fresh, expr)
                return fresh
            case e.Application(_, dfy_e.In(_), [x, y]):
                # Input: <x> in <y>
                # Constraints:
                #  - type(z3x) == elt_type(z3y)  (hard)
                #  - type(z3ret) == z3boolean     (hard)
                z3x = self.expr2z3(x)
                z3y = self.expr2z3(y)
                elt_type = self.elt_type(self.type(z3y))
                depth = max(self.get_depth(z3x), self.get_depth(z3y))
                self.add_soft_constraint(
                    self.type(z3x) == elt_type, x.position, f"bad_expr_{depth}"
                )
                z3ret = self.fresh_constant(self.term_sort, "term.")
                self.add_soft_constraint(
                    self.type(z3ret) == self.type2z3(boolean),
                    expr.position,
                    f"bad_expr_{depth}",
                )
                self.terms[str(z3ret)] = str(expr)
                return z3ret
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
                    case dfy_e.Neg(_):
                        name = "eudoxus.neg"
                        full_expr_type = self.type(self.expr2z3(args[0]))
                    case dfy_e.Power(_):
                        name = "eudoxus.div"
                        a0 = all_equal_types(args)
                        full_expr_type = self.type(a0)

                    case e.Implies(_):
                        name = "eudoxus.implies"
                        all_some_type(args, boolean)
                        full_expr_type = self.type2z3(boolean)
                    case dfy_e.IntDivide(_):
                        name = "eudoxus.intdiv"
                        a0 = all_some_type(args, integer)
                        full_expr_type = self.type2z3(integer)

                    case e.Modulo(_):
                        name = "eudoxus.mod"
                        a0 = all_some_type(args, integer)
                        full_expr_type = self.type2z3(integer)

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
                        self.type(full_expr) == full_expr_type, expr.position, "default"
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
                        self.has_len(self.type(z3args)), args[0].position, "default"
                    )
                    self.add_soft_constraint(
                        self.type(z3ret) == self.type2z3(integer),
                        expr.position,
                        "default",
                    )
                    self.terms[str(z3ret)] = str(expr)
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
                            "default",
                        )
                    z3ret = self.fresh_constant(self.term_sort, "term.")
                    self.add_soft_constraint(
                        self.type(z3ret)
                        == self.type2z3(
                            self.function_symbol_table[name]["return_type"]
                        ),
                        expr.position,
                        "default",
                    )
                    self.terms[str(z3ret)] = str(expr)
                    return z3ret

                else:
                    raise ValueError(f"Unsupported function {name}")

            case e.Variant(_, name):
                return self.variants[name]
            case dfy_e.Subscript(_, lst, index):
                # Input: <lst>[<index>]
                # Constraints:
                #  - type(z3index) == z3int
                #  - type(z3ret) == elt_type(z3lst)
                # need is_list(z3lst) to reject indexing into non_list
                z3lst = self.expr2z3(lst)
                self.add_soft_constraint(self.is_list(self.type(z3lst)), lst.position)
                if isinstance(index, dfy_e.Slice):
                    if index.start is not None:
                        z3start = self.expr2z3(index.start)
                        self.add_soft_constraint(
                            self.type(z3start) == self.type2z3(integer),
                            index.start.position,
                            f"bad_expr_{self.get_depth(z3start)}",
                        )
                    if index.end is not None:
                        z3end = self.expr2z3(index.end)
                        self.add_soft_constraint(
                            self.type(z3end) == self.type2z3(integer),
                            index.end.position,
                            f"bad_expr_{self.get_depth(z3end)}",
                        )
                    if index.step is not None:
                        z3step = self.expr2z3(index.step)
                        self.add_soft_constraint(
                            self.type(z3step) == self.type2z3(integer),
                            index.step.position,
                            f"bad_expr_{self.get_depth(z3step)}",
                        )

                    z3ret = self.fresh_constant(self.term_sort, "term.")
                    self.add_soft_constraint(
                        self.type(z3ret) == self.type(z3lst), expr.position, "default"
                    )
                else:
                    z3index = self.expr2z3(index)
                    self.add_soft_constraint(
                        self.type(z3index) == self.type2z3(integer),
                        index.position,
                        f"bad_expr_{self.get_depth(z3index)}",
                    )

                    z3ret = self.fresh_constant(self.term_sort, "term.")

                    self.add_soft_constraint(
                        self.type(z3ret) == self.elt_type(self.type(z3lst)),
                        expr.position,
                        f"bad_expr_{self.get_depth(z3lst)}",
                    )
                self.terms[str(z3ret)] = str(expr)

                return z3ret
            case dfy_e.Ite(_, cond, then_expr, else_expr):
                # Input: <then_expr> if <cond> else <else_expr>
                # Constraints:
                #  - type(z3cond) == z3boolean
                #  - type(z3then_expr) == type(z3else_expr)
                #  - type(z3ret) == type(z3then_expr)
                z3cond = self.expr2z3(cond)
                z3boolean = self.type2z3(boolean)
                self.add_soft_constraint(
                    self.type(z3cond) == z3boolean,
                    cond.position,
                    f"bad_expr_{self.get_depth(z3cond)}",
                )

                z3ret = self.fresh_constant(self.term_sort, "term.")
                z3then_expr = self.expr2z3(then_expr)
                z3else_expr = self.expr2z3(else_expr)
                self.add_soft_constraint(
                    self.type(z3then_expr) == self.type(z3else_expr),
                    then_expr.position,
                    "default",
                )
                self.add_soft_constraint(
                    self.type(z3ret) == self.type(z3then_expr), expr.position, "default"
                )
                self.terms[str(z3ret)] = str(expr)
                return z3ret
            case dfy_e.Set(_, content):
                if content is None:
                    z3ret = self.fresh_constant(self.term_sort, "term.")
                    self.add_soft_constraint(
                        self.is_list(self.type(z3ret)) == False,  # noqa: E712
                        expr.position,
                        "default",
                    )
                    self.add_soft_constraint(
                        self.has_len(self.type(z3ret)) == True,  # noqa: E712
                        expr.position,
                        "default",
                    )
                    self.terms[str(z3ret)] = str(expr)
                    return z3ret
                z3content = [self.expr2z3(item) for item in content]
                z3ret = self.fresh_constant(self.term_sort, "term.")
                self.add_soft_constraint(
                    self.is_list(self.type(z3ret)) == False,  # noqa: E712
                    expr.position,
                    "default",
                )
                self.add_soft_constraint(
                    self.has_len(self.type(z3ret)) == True,  # noqa: E712
                    expr.position,
                    "default",
                )
                self.add_soft_constraint(
                    self.elt_type(self.type(z3ret)) == self.type(z3content[0]),
                    expr.position,
                    "default",
                )
                self.terms[str(z3ret)] = str(expr)
                return z3ret
            case dfy_e.ForAll(_, variable, domain, predicate, condition):
                # Input: forall <variable> in <domain> | <condition> :: <predicate>
                # Constraints:
                #  - type(z3domain) == list_type
                #  - type(z3predicate) == z3boolean
                #  - type(z3ret) == z3boolean
                #  - type(z3cond) == z3boolean
                self.variables[variable.name] = self.fresh_constant(
                    self.term_sort, "term." + variable.name + "."
                )
                if domain.callee.name == "range":
                    for a in domain.arguments:
                        self.add_soft_constraint(
                            self.type(self.expr2z3(a)) == self.type2z3(integer),
                            a.position,
                            f"bad_expr_{self.get_depth(self.expr2z3(a))}",
                        )
                else:
                    z3domain = self.expr2z3(domain)
                    self.add_soft_constraint(
                        self.has_len(self.type(z3domain)),
                        domain.position,
                        f"bad_expr_{self.get_depth(z3domain)}",
                    )

                z3ret = self.fresh_constant(self.term_sort, "term.")
                z3predicate = self.expr2z3(predicate)
                z3boolean = self.type2z3(boolean)
                z3cond = self.expr2z3(condition) if condition is not None else None

                self.add_soft_constraint(
                    self.type(z3predicate) == z3boolean,
                    predicate.position,
                    f"bad_expr_{self.get_depth(z3predicate)}",
                )
                self.add_soft_constraint(
                    self.type(z3ret) == z3boolean, expr.position, "default"
                )

                if z3cond is not None:
                    self.add_soft_constraint(
                        self.type(z3cond) == z3boolean,
                        condition.position,
                        f"bad_expr_{self.get_depth(z3cond)}",
                    )

                return z3ret
            case dfy_e.EmptyList(_):
                z3ret = self.fresh_constant(self.term_sort, "term.")
                self.add_soft_constraint(
                    self.is_list(self.type(z3ret)) == True,  # noqa: E712
                    expr.position,
                    "default",
                )
                self.add_soft_constraint(
                    self.has_len(self.type(z3ret)) == True,  # noqa: E712
                    expr.position,
                    "default",
                )
                self.terms[str(z3ret)] = str(expr)
                return z3ret
            case dfy_e.IsInstance(_, expr, ty):
                # Input: <expr> is <ty>
                # Constraints:
                #  - type(z3expr) == z3ty
                #  - type(z3ret) == z3boolean
                z3expr = self.expr2z3(expr)
                z3ty = self.type2z3(ty)
                z3ret = self.fresh_constant(self.term_sort, "term.")
                z3boolean = self.type2z3(boolean)
                self.add_soft_constraint(
                    self.type(z3expr) == z3ty,
                    expr.position,
                    f"bad_expr_{self.get_depth(z3expr)}",
                )
                self.add_soft_constraint(
                    self.type(z3ret) == z3boolean, expr.position, "default"
                )
                self.terms[str(z3ret)] = str(expr)
                return z3ret
            case Hole(_):
                return self.fresh_constant(self.term_sort, "term.")
            case _:
                raise ValueError(f"Unsupported expression {expr}")

    def check(self, modules: List[Module]) -> Dict[Position, Node]:
        for module in modules:
            if module.method_or_function == "method":
                self.decl2z3(s.Variable(None, module.ret_name, module.return_type))
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
                            self.type(value)
                            == self.type(self.variables[module.ret_name.name]),
                            pos,
                            "default",
                        )
                    else:
                        self.stmt2z3(stmt)
            elif module.method_or_function == "function":
                self.expr2z3(module.body)
            else:
                raise ValueError(f"Unsupported module type {module.method_or_function}")

        positions, model = self.solve()

        positions = positions + self.input_holes
        # import ipdb; ipdb.set_trace()

        holes = {}
        for pos in positions:
            if pos in self.to_repair:
                original_term, original_node = self.to_repair[pos]
                assigned_term = model.eval(original_term, model_completion=True)
                holes[pos] = self.repair(model, original_node, assigned_term)
            else:
                holes[pos] = Hole(pos)

        return holes
