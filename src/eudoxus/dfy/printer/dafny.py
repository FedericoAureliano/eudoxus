from typing import List

import eudoxus.ast.expression as e
import eudoxus.ast.proof as p
import eudoxus.ast.statement as s
import eudoxus.ast.type as t
from eudoxus.ast.module import Module
from eudoxus.ast.node import Hole
from eudoxus.dfy.ast.list import List as ListType
from eudoxus.dfy.ast.params import Param, Params
from eudoxus.dfy.ast.statement import Ensures, Requires, Return
from eudoxus.printer.uclid import expr2ucl


def type2ucl(output, type: t.Type):
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
            type2ucl(output, elem_t)
            output.write(">")

        case Hole(_):
            output.write("??")
        case _:
            raise ValueError(f"Unsupported type {type}")


def return_type2dfy(output, return_type: t.Type):
    output.write(" : ")
    type2ucl(output, return_type)


def requires2dfy(output, requires: List[Requires]):
    for r in requires:
        output.write("requires( ")
        expr2ucl(output, r.condition)
        output.write(" );\n")


def ensures2dfy(output, ensures: Ensures):
    for ens in ensures:
        output.write("ensures( ")
        expr2ucl(output, ens.condition)
        output.write(" );\n")


def module2dfy(output, module: Module, indent):
    """
    Note that this uses module for consistency with ucl
    but is actually a method or a function in dafny.
    """
    name = module.name.name
    method_or_function = module.method_or_function
    if method_or_function == "method":
        output.write(f"{method_or_function} {name}")
        params2dfy(output, module.params)
        output.write(" returns (result")
        return_type2dfy(output, module.return_type)

        output.write(")\n")
        requires2dfy(output, module.requires)
        ensures2dfy(output, module.ensures)

        # return_statement2dfy(output, )
        output.write("{\n")
        indent += 1
        for statement in module.body.statements:
            stmt2dfy(output, statement, indent)
        output.write("}\n")
    else:
        raise NotImplementedError


def params2dfy(output, params: Params) -> str:
    output.write("(")

    for i, param in enumerate(params.params):
        param2dfy(output, param)
        if i < len(params) - 1:
            output.write(", ")
    output.write(")")


def param2dfy(output, param: Param) -> str:
    output.write(f"{param.name.name} :")
    type2ucl(output, param.type)


def stmt2dfy(output, stmt: s.Statement, indent):
    space = "  " * indent
    match stmt:
        case s.Assignment(_, target, value) if isinstance(target, e.Identifier):
            target = target.name
            output.write(space + target)
            output.write(" := ")
            expr2ucl(output, value)
            output.write(";\n")
        case s.If(_, cond, body, orelse):
            output.write(space)
            output.write("if (")
            expr2ucl(output, cond)
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
            expr2ucl(output, cond)
            output.write(";\n")
        case s.Assert(_, cond):
            output.write(space + "assert ")
            expr2ucl(output, cond)
            output.write(";\n")
        case Hole(_):
            output.write(space + "??;\n")
        case Return(_, value):
            output.write(space + "return ")
            expr2ucl(output, value)
            output.write(";\n")
        case Requires(_, cond):
            output.write(space + "requires( ")
            expr2ucl(output, cond)
            output.write(");\n")

        case Ensures(_, cond):
            output.write(space + "ensures( ")
            expr2ucl(output, cond)
            output.write(");\n")
        case _:
            raise ValueError(f"Unsupported statement {stmt}")


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
