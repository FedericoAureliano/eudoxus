from typing import List

import eudoxus.ast.expression as e
import eudoxus.ast.proof as p
import eudoxus.ast.statement as s
import eudoxus.ast.type as t
from eudoxus.ast.module import Module
from eudoxus.ast.node import Hole
from eudoxus.dfy.ast import expression as dfy_e
from eudoxus.dfy.ast import statement as dfy_s
from eudoxus.dfy.ast.list_and_sets import ListType, SetType
from eudoxus.dfy.ast.params import Param, Params
from eudoxus.dfy.ast.string import StringType
from eudoxus.printer.uclid import op2ucl

ANNOTATIONS = True
COMMENTS = False


def type2dfy(output, type: t.Type):
    match type:
        case t.Boolean(_):
            output.write("bool")
        case t.Integer(_):
            output.write("int")
        case t.Float(_):
            output.write("float")
        case t.BitVector(_, size):
            output.write(f"bv{size}")
        case ListType(_, elem_t):
            output.write("seq<")
            type2dfy(output, elem_t)
            output.write(">")
        case SetType(_, elem_t):
            output.write("set<")
            type2dfy(output, elem_t)
            output.write(">")
        case StringType(_):
            output.write("string")
        case Hole(_):
            output.write("??")
        case _:
            raise ValueError(f"Unsupported type {type}")


def return_type2dfy(output, return_type: t.Type):
    output.write(" : ")
    type2dfy(output, return_type)


def requires2dfy(output, requires: List[dfy_s.Requires]):
    for r in requires:
        if not isinstance(r.condition, dfy_e.IsInstance):
            output.write("requires( ")
            expr2dfy(output, r.condition)
            output.write(" );\n")


def ensures2dfy(output, ensures: dfy_s.Ensures):
    for ens in ensures:
        if not isinstance(ens.condition, dfy_e.IsInstance):
            output.write("ensures( ")
            expr2dfy(output, ens.condition)
            output.write(" );\n")


def decreases2dfy(output, decreases: dfy_s.Decreases):
    for dec in decreases:
        output.write("decreases( ")
        expr2dfy(output, dec.condition)
        output.write(" );\n")


def module2dfy(output, module: Module, indent, annotations=True, comments=True):
    """
    Note that this uses module for consistency with ucl
    but is actually a method or a function in dafny.
    """
    global ANNOTATIONS
    global COMMENTS
    ANNOTATIONS = annotations
    COMMENTS = comments
    # TODO: this should be done as a class, but using a function for now
    name = module.name.name
    method_or_function = module.method_or_function
    if method_or_function == "method":
        output.write(f"{method_or_function} {name}")
        params2dfy(output, module.params)
        output.write(" returns (")
        if module.ret_name is not None:
            output.write(module.ret_name.name)
        else:
            output.write("result")
        return_type2dfy(output, module.return_type)

        output.write(")\n")
        if ANNOTATIONS:
            requires2dfy(output, module.requires)
            ensures2dfy(output, module.ensures)
            decreases2dfy(output, module.decreases)

        # return_statement2dfy(output, )
        output.write("{\n")
        indent += 1
        for statement in module.body.statements:
            stmt2dfy(output, statement, indent)
        output.write("}\n")
    elif method_or_function == "function":
        output.write(f"{method_or_function} method {name}")
        params2dfy(output, module.params)
        output.write(" : ")
        type2dfy(output, module.return_type)
        output.write("\n")
        if ANNOTATIONS:
            requires2dfy(output, module.requires)
        ensures2dfy(output, module.ensures)
        output.write(" {\n")
        indent += 1
        space = "  " * indent
        output.write(space)
        expr2dfy(output, module.body)
        output.write("\n}\n")

    else:
        raise ValueError(
            f"Unsupported {method_or_function} is not a method or function"
        )


def params2dfy(output, params: Params) -> str:
    output.write("(")

    for i, param in enumerate(params.params):
        param2dfy(output, param)
        if i < len(params) - 1:
            output.write(", ")
    output.write(")")


def param2dfy(output, param: Param) -> str:
    output.write(f"{param.name.name} :")
    type2dfy(output, param.type)


def stmt2dfy(output, stmt: s.Statement, indent):
    space = "  " * indent
    match stmt:
        case s.Assignment(_, target, value) if isinstance(target, e.Identifier):
            target = target.name
            output.write(space + target)
            output.write(" := ")
            expr2dfy(output, value)
            output.write(";\n")
        case dfy_s.DeclAssignment(_, target, value, ty) if isinstance(
            target, e.Identifier
        ):
            target = target.name

            output.write(space + f"var {target} : ")
            type2dfy(output, ty)
            output.write(" := ")
            expr2dfy(output, value)
            output.write(";\n")
        case s.If(_, cond, body, orelse):
            output.write(space)
            output.write("if (")
            expr2dfy(output, cond)
            output.write(") {\n")
            stmt2dfy(output, body, indent + 1)
            if orelse.statements != []:
                output.write(space + "} else {\n")
                stmt2dfy(output, orelse, indent + 1)
            output.write(space + "}\n")
        case s.Skip(_):
            pass
        case s.Block(_, stmts):
            if stmts:
                for stmt in stmts:
                    stmt2dfy(output, stmt, indent)
            else:
                pass
        case s.Havoc(_, target):
            name = target.name
            output.write(space + name + " = *" + ";\n")
        case s.Assume(_, cond):
            output.write(space + "assume ")
            expr2dfy(output, cond)
            output.write(";\n")
        case s.Assert(_, cond):
            output.write(space + "assert ")
            expr2dfy(output, cond)
            output.write(";\n")
        case Hole(_):
            output.write(space + "??;\n")
        case dfy_s.Return(_, value):
            output.write(space + "return ")
            expr2dfy(output, value)
            output.write(";\n")
        case dfy_s.Requires(_, cond):
            if ANNOTATIONS:
                output.write(space + "requires( ")
                expr2dfy(output, cond)
                output.write(");\n")

        case dfy_s.Ensures(_, cond):
            if ANNOTATIONS:
                output.write(space + "ensures( ")
                expr2dfy(output, cond)
                output.write(");\n")
        case dfy_s.While(_, cond, invariant, decreases, body):
            output.write(space + "while (")
            expr2dfy(output, cond)
            output.write(")\n")

            for inv in invariant:
                if ANNOTATIONS:
                    output.write(space + "invariant(")
                    expr2dfy(output, inv.condition)
                    output.write(");\n")
            for dec in decreases:
                if ANNOTATIONS:
                    output.write(space + "decreases(")
                    expr2dfy(output, dec.condition)
                    output.write(");\n")
            output.write(space + "{\n")
            stmt2dfy(output, body, indent + 1)
            output.write(space + "}\n")
        case dfy_s.Comment(_, comment):
            if COMMENTS:
                output.write(space + comment.replace("#", "//", 1) + "\n")
        case dfy_s.Append(_, lst, item):
            output.write(space)
            output.write(lst.name + f":= {lst.name} + [")
            expr2dfy(output, item)
            output.write("];\n")
        case _:
            raise ValueError(f"Unsupported statement {stmt}")


def expr2dfy(output, expr: e.Expression):
    match expr:
        case e.Variant(_, name):
            output.write(name)
        case e.Selection(_, target, field):
            expr2dfy(output, target)
            output.write(".")
            output.write(field.name)
        case e.Application(_, name, args) if isinstance(name, e.Identifier):
            name = name.name
            if name == "len":
                assert len(args) == 1
                output.write("|")
                for i, a in enumerate(args):
                    if i > 0:
                        output.write(", ")
                    expr2dfy(output, a)
                output.write("|")
            else:
                if name == "set":
                    name = "cast_to_set"
                output.write(name)
                if len(args) > 0:
                    output.write("(")
                    for i, a in enumerate(args):
                        if i > 0:
                            output.write(", ")
                        expr2dfy(output, a)
                    output.write(")")
        case e.Application(_, op, args) if isinstance(op, e.Operator):
            match op:
                case e.Quantifier(_, bindings):
                    name = "forall" if isinstance(op, e.Forall) else "exists"
                    output.write("(")
                    output.write(name)
                    output.write(" (")
                    for i, (n, ty) in enumerate(bindings):
                        if i > 0:
                            output.write(", ")
                        output.write(n.name)
                        output.write(": ")
                        type2dfy(output, ty)
                    output.write(") :: ")
                    expr2dfy(output, args[0])
                    output.write(")")
                case e.Not(_):
                    op2ucl(output, op)
                    output.write("(")
                    expr2dfy(output, args[0])
                    output.write(")")
                case e.Add(_) | e.Subtract(_) | e.Multiply(_) | e.Divide(_) | e.Modulo(
                    _
                ) | e.And(_) | e.Or(_):
                    for i, a in enumerate(args):
                        if i > 0:
                            output.write(" ")
                            op2ucl(output, op)
                            output.write(" ")
                        expr2dfy(output, a)
                case e.Equal(_) | e.NotEqual(_) | e.LessThan(_) | e.GreaterThan(
                    _
                ) | e.LessThanOrEqual(_) | e.GreaterThanOrEqual(_):
                    expr2dfy(output, args[0])
                    for i, a in enumerate(args[1:]):
                        output.write(" ")
                        op2ucl(output, op)
                        output.write(" ")
                        expr2dfy(output, a)
                        if i < len(args) - 2:
                            output.write(" ")
                            op2ucl(output, e.And(op.position))
                            output.write(" ")
                            expr2dfy(output, args[i + 1])
                case dfy_e.In(_):
                    expr2dfy(output, args[0])
                    output.write(" in ")
                    expr2dfy(output, args[1])
                case dfy_e.Neg(_):
                    output.write("-")
                    expr2dfy(output, args[0])
                case dfy_e.Power(_):
                    output.write("power(")
                    expr2dfy(output, args[0])
                    output.write(", ")
                    expr2dfy(output, args[1])
                    output.write(")")
                case e.Implies(_):
                    expr2dfy(output, args[0])
                    output.write(" ==> ")
                    expr2dfy(output, args[1])
                case _:
                    raise ValueError(f"Unsupported operator {op}")
        case e.Boolean(_, value) | e.Integer(_, value):
            output.write(str(value).lower())
        case e.BitVector(_, value, width):
            output.write(f"{value}bv{width}")
        case Hole(_):
            output.write("??")
        case dfy_e.Subscript(_, list_value, subscript):
            expr2dfy(output, list_value)
            output.write("[")
            expr2dfy(output, subscript)
            output.write("]")
        case dfy_e.Slice(_, start, end, step):
            if start:
                expr2dfy(output, start)
            output.write("..")
            if end:
                expr2dfy(output, end)
            if step:
                print("step is currently not supported")
                # TODO: support reverse and maybe implement a built in
        case dfy_e.Ite(_, condition, then_expr, else_expr):
            output.write("if ")
            expr2dfy(output, condition)
            output.write(" then ")
            expr2dfy(output, then_expr)
            output.write(" else ")
            expr2dfy(output, else_expr)
        case dfy_e.ForAll(_, variable, domain, predicate, condition):
            output.write("forall ")

            output.write(variable.name)

            if condition is not None:
                output.write(" | ")
                expr2dfy(output, condition)
            output.write(" :: ")
            if domain.callee.name == "range":
                maximum = domain.arguments[0]
                output.write(f"(0 <= {variable.name} && {variable.name} < ")
                expr2dfy(output, maximum)
                output.write(")")
            else:
                output.write(variable.name)
                output.write(" in ")
                expr2dfy(output, domain)
            output.write(" ==> ")
            expr2dfy(output, predicate)
        case dfy_e.EmptyList(_):
            output.write("[]")

        case dfy_e.Set(_, content):
            output.write("{")
            if content is not None:
                for c in content:
                    expr2dfy(output, c)
            output.write("}")

        case _:
            raise ValueError(f"Unsupported expression {expr}")


def cmd2ucl(output, cmd: p.Command, indent):
    space = "  " * indent
    match cmd:
        case p.Block(_, cmds):
            for cmd in cmds:
                cmd2ucl(output, cmd, indent)
        case p.Induction(_, k):
            output.write(f"{space}induction({k});\n")
            output.write(f"{space}check;\n")
            output.write(f"{space}print_results;\n")
        case p.BoundedModelChecking(_, k):
            output.write(f"{space}bmc({k});\n")
            output.write(f"{space}check;\n")
            output.write(f"{space}print_results;\n")
        case _:
            raise ValueError(f"Unsupported command {cmd}")
