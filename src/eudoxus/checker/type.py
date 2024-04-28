from typing import Dict, List, Tuple

import z3

import eudoxus.ast.expression as e
import eudoxus.ast.module as m
import eudoxus.ast.node as n
import eudoxus.ast.proof as p
import eudoxus.ast.statement as s
import eudoxus.ast.type as t
from eudoxus.ast.node import Identifier, Node, Position
from eudoxus.checker.interface import Checker
from eudoxus.utils import foldl


def get_leafs(parent, mod):
    leafs = {}
    for name, cls in mod.__dict__.items():
        if (
            isinstance(cls, type)
            and issubclass(cls, parent)
            and cls.__module__ == mod.__name__
        ):
            leafs[name] = cls

    to_delete = set()
    for n1, c1 in leafs.items():
        for n2, c2 in leafs.items():
            if n1 != n2 and issubclass(c1, c2):
                to_delete.add(n2)

    for ni in to_delete:
        del leafs[ni]

    return leafs


class Universe:
    def __init__(self):
        self.symbol = z3.DeclareSort("Symbol")

        self.expr = z3.Datatype(e.Expression.__name__)
        self.type = z3.Datatype(t.Type.__name__)
        self.stmt = z3.Datatype(s.Statement.__name__)
        self.cmd = z3.Datatype(p.Command.__name__)
        self.mod = z3.Datatype(m.Module.__name__)

        self.expr_list = z3.Datatype(f"{e.Expression.__name__}_list")
        self.expr_list.declare("empty")
        self.expr_list.declare("cons", ("head", self.expr), ("tail", self.expr_list))

        self.type_list = z3.Datatype(f"{t.Type.__name__}_list")
        self.type_list.declare("empty")
        self.type_list.declare("cons", ("head", self.type), ("tail", self.type_list))

        self.stmt_list = z3.Datatype(f"{s.Statement.__name__}_list")
        self.stmt_list.declare("empty")
        self.stmt_list.declare("cons", ("head", self.stmt), ("tail", self.stmt_list))

        self.cmd_list = z3.Datatype(f"{p.Command.__name__}_list")
        self.cmd_list.declare("empty")
        self.cmd_list.declare("cons", ("head", self.cmd), ("tail", self.cmd_list))

        self.symbol_list = z3.Datatype(f"{Identifier.__name__}_list")
        self.symbol_list.declare("empty")
        self.symbol_list.declare(
            "cons", ("head", self.symbol), ("tail", self.symbol_list)
        )

        self.id_type_pair = z3.Datatype("id_type_pair")
        self.id_type_pair.declare("pair", ("id", self.symbol), ("type", self.type))

        self.id_type_pair_list = z3.Datatype("id_type_pair_list")
        self.id_type_pair_list.declare("empty")
        self.id_type_pair_list.declare(
            "cons", ("head", self.id_type_pair), ("tail", self.id_type_pair_list)
        )

        self.id_expr_pair = z3.Datatype("id_expr_pair")
        self.id_expr_pair.declare("pair", ("id", self.symbol), ("expr", self.expr))

        self.id_expr_pair_list = z3.Datatype("id_expr_pair_list")
        self.id_expr_pair_list.declare("empty")
        self.id_expr_pair_list.declare(
            "cons", ("head", self.id_expr_pair), ("tail", self.id_expr_pair_list)
        )

        expr_leafs = get_leafs(e.Expression, e)
        type_leafs = get_leafs(t.Type, t)
        stmt_leafs = get_leafs(s.Statement, s)
        cmd_leafs = get_leafs(p.Command, p)
        mod_leafs = get_leafs(m.Module, m)

        def declare_from_leafs(leafs, adt):
            for name, cls in leafs.items():
                fields = []
                for field_name, field_type in cls.__annotations__.items():
                    if field_type == int:
                        field_type = z3.IntSort()
                    elif field_type == bool:
                        field_type = z3.BoolSort()
                    elif field_type == Identifier or field_type == str:
                        field_type = self.symbol
                    elif field_type == e.Expression:
                        field_type = self.expr
                    elif field_type == t.Type:
                        field_type = self.type
                    elif field_type == s.Statement:
                        field_type = self.stmt
                    elif field_type == p.Command:
                        field_type = self.cmd
                    elif field_type == List[e.Expression]:
                        field_type = self.expr_list
                    elif field_type == List[t.Type]:
                        field_type = self.type_list
                    elif field_type == List[s.Statement]:
                        field_type = self.stmt_list
                    elif field_type == List[p.Command]:
                        field_type = self.cmd_list
                    elif field_type == List[n.Identifier]:
                        field_type = self.symbol_list
                    elif field_type == List[Tuple[n.Identifier, t.Type]]:
                        field_type = self.id_type_pair_list
                    elif field_type == List[Tuple[n.Identifier, e.Expression]]:
                        field_type = self.id_expr_pair_list
                    else:
                        raise NotImplementedError(
                            f"Unsupported field type {field_type} for {field_name}"
                        )
                    fields.append((field_name, field_type))
                adt.declare(name, *fields)

        declare_from_leafs(expr_leafs, self.expr)
        declare_from_leafs(type_leafs, self.type)
        declare_from_leafs(stmt_leafs, self.stmt)
        declare_from_leafs(cmd_leafs, self.cmd)
        declare_from_leafs(mod_leafs, self.mod)

        (
            self.mod,
            self.expr,
            self.type,
            self.stmt,
            self.cmd,
            self.expr_list,
            self.type_list,
            self.stmt_list,
            self.cmd_list,
            self.symbol_list,
            self.id_type_pair,
            self.id_type_pair_list,
            self.id_expr_pair,
            self.id_expr_pair_list,
        ) = z3.CreateDatatypes(
            self.mod,
            self.expr,
            self.type,
            self.stmt,
            self.cmd,
            self.expr_list,
            self.type_list,
            self.stmt_list,
            self.cmd_list,
            self.symbol_list,
            self.id_type_pair,
            self.id_type_pair_list,
            self.id_expr_pair,
            self.id_expr_pair_list,
        )


class TypeChecker(Checker):
    def reason_to_weight(self, reason: str) -> int:
        match reason:
            case "bad_constant":
                return 1
            case "bad_type":
                return 100
            case "bad_identifier":
                return 1000
        return 10

    def encode(self, cls, pos, children) -> Node:
        match cls:
            case m.Module:
                # Hard: type(spec) == bool
                spec = children[9]
                self.add_hard_constraint(
                    self.type_of(spec) == self.universe.type.BooleanType
                )
                return self.universe.mod.Module(*children)
            case n.Identifier:
                # Input: x
                # Soft: x == x'
                # Output: x'
                x = children[0]
                if x not in self.name_map:
                    self.name_map[x] = self.fresh_constant(self.universe.symbol, x)
                xp = self.fresh_constant(self.universe.symbol, x)
                x = self.name_map[x]
                self.add_soft_constraint(x == xp, pos, "bad_identifier")
                return xp
            case t.IntegerType:
                # Input: int
                # Soft: int == int'
                # Output: int'
                intp = self.fresh_constant(self.universe.type, "IntegerType")
                self.add_soft_constraint(
                    self.universe.type.IntegerType == intp, pos, "bad_type"
                )
                return intp
            case t.BooleanType:
                # Input: bool
                # Soft: bool == bool'
                # Output: bool'
                boolp = self.fresh_constant(self.universe.type, "BooleanType")
                self.add_soft_constraint(
                    self.universe.type.BooleanType == boolp, pos, "bad_type"
                )
                return boolp
            case t.BitVectorType:
                # Input: BitVector(w)
                # Soft: w == w'
                # Output: BitVector(w')
                w = children[0]
                wp = self.fresh_constant(z3.IntSort(), str(w))
                self.add_soft_constraint(w == wp, pos, "bad_type")
                return self.universe.type.BitVectorType(wp)
            case s.Block:
                arg = foldl(
                    lambda x, y: self.universe.stmt_list.cons(y, x),
                    self.universe.stmt_list.empty,
                    children[0],
                )
                return self.universe.stmt.Block(arg)
            case s.Assignment:
                # Input: x = y;
                # Hard: type(x) == type(y)
                # Output: x = y;
                x = children[0]
                y = children[1]
                self.add_hard_constraint(self.type_of(x) == self.type_of(y))
                return self.universe.stmt.Assignment(x, y)
            case s.LocalDecl | s.OutputDecl | s.InputDecl | s.SharedDecl:
                # Input: var x: t;
                # Hard: type(x) == t
                # Output: var x: t;
                xsym = children[0]
                xapp = self.universe.expr.FunctionApplication(
                    xsym, self.universe.expr_list.empty
                )
                tz3 = children[1]
                self.add_hard_constraint(self.type_of(xapp) == tz3)
                return self.universe.stmt.LocalDecl(xsym, tz3)
            case s.InstanceDecl:
                # Input: instance target: mod(pairs);
                target = children[0]
                mod = children[1]
                pairs = children[2]

                def to_pair(pair):
                    id = pair[0]
                    expr = pair[1]
                    return self.universe.id_expr_pair.pair(id, expr)

                arg = foldl(
                    lambda acc, z: self.universe.id_expr_pair_list.cons(
                        to_pair(z), acc
                    ),
                    self.universe.id_expr_pair_list.empty,
                    pairs,
                )
                return self.universe.stmt.InstanceDecl(target, mod, arg)
            case s.If:
                # Input: if c then t else e
                # Hard: type(c) == bool
                # Output: if c then t else e
                cz3 = children[0]
                tc3 = children[1]
                ez3 = children[2]
                self.add_hard_constraint(
                    self.type_of(cz3) == self.universe.type.BooleanType
                )
                return self.universe.stmt.If(cz3, tc3, ez3)
            case s.Assert:
                # Input: assert c
                # Hard: type(c) == bool
                # Output: assert c
                cz3 = children[0]
                self.add_hard_constraint(
                    self.type_of(cz3) == self.universe.type.BooleanType
                )
                return self.universe.stmt.Assert(cz3)
            case s.Assume:
                # Input: assume c
                # Hard: type(c) == bool
                # Output: assume c
                cz3 = children[0]
                self.add_hard_constraint(
                    self.type_of(cz3) == self.universe.type.BooleanType
                )
                return self.universe.stmt.Assume(cz3)
            case e.IntegerValue:
                # Input: IntegerValue(z)
                # Hard: type(z') == int
                # Soft: z == z'
                # Output: z'
                z = children[0]
                zz3 = self.universe.expr.IntegerValue(z)
                zp = self.fresh_constant(self.universe.expr, str(z))
                self.add_hard_constraint(
                    self.type_of(zz3) == self.universe.type.IntegerType
                )
                self.add_soft_constraint(zz3 == zp, pos, "bad_constant")
                return zp
            case e.BooleanValue:
                # Input: BooleanValue(b)
                # Hard: type(b') == bool
                # Soft: b == b'
                # Output: b'
                b = children[0]
                bz3 = self.universe.expr.BooleanValue(b)
                bp = self.fresh_constant(self.universe.expr, str(b))
                self.add_hard_constraint(
                    self.type_of(bz3) == self.universe.type.BooleanType
                )
                self.add_soft_constraint(bz3 == bp, pos, "bad_constant")
                return bp
            case e.Add:
                # Input: x + y
                # Hard: type(x) == type(y)
                # Hard: type(x + y) == type(x)
                # Output: x + y
                x = children[0]
                y = children[1]
                x_plus_y = self.universe.expr.Add(x, y)
                self.add_hard_constraint(self.type_of(x) == self.type_of(y))
                self.add_hard_constraint(self.type_of(x_plus_y) == self.type_of(x))
                return x_plus_y
            case e.GreaterThan:
                # Input: x > y
                # Hard: type(x) == type(y)
                # Hard: type(x > y) == bool
                # Output: x > y
                x = children[0]
                y = children[1]
                x_gt_y = self.universe.expr.GreaterThan(x, y)
                self.add_hard_constraint(self.type_of(x) == self.type_of(y))
                self.add_hard_constraint(
                    self.type_of(x_gt_y) == self.universe.type.BooleanType
                )
                return x_gt_y
            case e.GreaterThanOrEqual:
                # Input: x >= y
                # Hard: type(x) == type(y)
                # Hard: type(x >= y) == bool
                # Output: x >= y
                x = children[0]
                y = children[1]
                x_ge_y = self.universe.expr.GreaterThanOrEqual(x, y)
                self.add_hard_constraint(self.type_of(x) == self.type_of(y))
                self.add_hard_constraint(
                    self.type_of(x_ge_y) == self.universe.type.BooleanType
                )
                return x_ge_y
            case e.LessThan:
                # Input: x < y
                # Hard: type(x) == type(y)
                # Hard: type(x < y) == bool
                # Output: x < y
                x = children[0]
                y = children[1]
                x_lt_y = self.universe.expr.LessThan(x, y)
                self.add_hard_constraint(self.type_of(x) == self.type_of(y))
                self.add_hard_constraint(
                    self.type_of(x_lt_y) == self.universe.type.BooleanType
                )
                return x_lt_y
            case e.LessThanOrEqual:
                # Input: x <= y
                # Hard: type(x) == type(y)
                # Hard: type(x <= y) == bool
                # Output: x <= y
                x = children[0]
                y = children[1]
                x_le_y = self.universe.expr.LessThanOrEqual(x, y)
                self.add_hard_constraint(self.type_of(x) == self.type_of(y))
                self.add_hard_constraint(
                    self.type_of(x_le_y) == self.universe.type.BooleanType
                )
                return x_le_y
            case e.And:
                # Input: x and y
                # Hard: type(x) == type(y) == bool
                # Hard: type(x and y) == bool
                # Output: x and y
                x = children[0]
                y = children[1]
                x_and_y = self.universe.expr.And(x, y)
                self.add_hard_constraint(
                    self.type_of(x) == self.universe.type.BooleanType
                )
                self.add_hard_constraint(
                    self.type_of(y) == self.universe.type.BooleanType
                )
                self.add_hard_constraint(
                    self.type_of(x_and_y) == self.universe.type.BooleanType
                )
                return x_and_y
            case e.Not:
                # Input: not x
                # Hard: type(x) == bool
                # Hard: type(not x) == bool
                # Output: not x
                x = children[0]
                not_x = self.universe.expr.Not(x)
                self.add_hard_constraint(
                    self.type_of(x) == self.universe.type.BooleanType
                )
                self.add_hard_constraint(
                    self.type_of(not_x) == self.universe.type.BooleanType
                )
                return not_x
            case e.FunctionApplication:
                arg = foldl(
                    lambda x, y: self.universe.expr_list.cons(y, x),
                    self.universe.expr_list.empty,
                    children[1],
                )
                return self.universe.expr.FunctionApplication(children[0], arg)
            case p.Block:
                arg = foldl(
                    lambda x, y: self.universe.cmd_list.cons(y, x),
                    self.universe.cmd_list.empty,
                    children[0],
                )
                return self.universe.cmd.Block(arg)
            case p.Induction:
                # Input: induction(k)
                # Output: induction(k)
                k = children[0]
                return self.universe.cmd.Induction(k)
            case _:
                raise NotImplementedError(f"Unsupported class {cls}")

    def z3_to_ast(self, z3expr, node, position) -> Node:
        def is_int(x):
            return self.model.eval(
                self.universe.type.is_IntegerType(x), model_completion=True
            )

        def is_bool(x):
            return self.model.eval(
                self.universe.type.is_BooleanType(x), model_completion=True
            )

        def is_bv(x):
            return self.model.eval(
                self.universe.type.is_BitVectorType(x), model_completion=True
            )

        match z3expr.sort():
            case self.universe.type:
                if is_int(z3expr):
                    return t.IntegerType(position)
                elif is_bool(z3expr):
                    return t.BooleanType(position)
                elif is_bv(z3expr):
                    w = self.model.eval(self.universe.type.width(z3expr))
                    return t.BitVectorType(position, w)
            case self.universe.expr:
                new_type = self.type_of(z3expr)
                match node:
                    case e.IntegerValue(_, v) if is_bool(new_type):
                        return e.BooleanValue(position, False if v == 0 else True)
                    case e.IntegerValue(_, _) if is_int(new_type):
                        return node
                    case e.IntegerValue(_, v) if is_bv(new_type):
                        w = self.model.eval(self.universe.type.width(new_type))
                        return e.BitVectorValue(position, v, w)
                    case e.BooleanValue(_, v) if is_int(new_type):
                        return e.IntegerValue(position, 1 if v else 0)
                    case e.BooleanValue(_, _) if is_bool(new_type):
                        return node

        return None

    def repair(self, cls, pos, children) -> Node:
        if pos in self.to_repair:
            z3expr = self.pos_to_z3expr[pos]
            node = self.pos_to_node[pos]
            new_node = self.z3_to_ast(z3expr, node, pos)
            if new_node is not None:
                self.to_repair[pos] = new_node

        return cls(pos, *children)

    def check(self, modules: List[m.Module]) -> Dict[Position, Node]:
        self.universe = Universe()
        self.type_of = self.declare_function(
            "TypeOf", self.universe.expr, self.universe.type
        )
        self.name_map = {}
        self.pos_to_z3expr = {}
        self.pos_to_node = {}

        def visit_and_save(cls, pos, children):
            node = cls(pos, *children)
            self.pos_to_node[pos] = node
            return node

        def encode_and_save(cls, pos, children):
            node = self.encode(cls, pos, children)
            self.pos_to_z3expr[pos] = node
            return node

        for module in modules:
            module.visit(visit_and_save)
            module.visit(encode_and_save)

        positions, self.model = self.solve()

        self.to_repair = {position: n.Hole(position) for position in positions}

        for module in modules:
            module.visit(self.repair)

        return self.to_repair
