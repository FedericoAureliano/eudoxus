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
from eudoxus.printer.python import op2py

ANNOTATIONS = True
COMMENTS = False
IMPORTS = set()


def type2py(output, type: t.Type):
    match type:
        case t.Boolean(_):
            output.write("bool")
        case t.Integer(_):
            output.write("int")
        case t.Float(_):
            output.write("float")
        case t.BitVector(_, _):
            output.write("??")
        case ListType(_, elem_t):
            output.write("List[")
            type2py(output, elem_t)
            output.write("]")
        case SetType(_, elem_t):
            output.write("Set[")
            type2py(output, elem_t)
            output.write("]")
        case StringType(_):
            output.write("str")
        case Hole(_):
            output.write("??")
        case _:
            output.write("??")


def requires2py(output, requires: List[dfy_s.Requires], indent):
    space = "  " * indent
    for r in requires:
        if not isinstance(r.condition, dfy_e.IsInstance):
            output.write(f"{space}dafnypy.requires( ")
            expr2py(output, r.condition)
            output.write(" )\n")


def ensures2py(output, ensures: dfy_s.Ensures, indent):
    space = "  " * indent
    for ens in ensures:
        if not isinstance(ens.condition, dfy_e.IsInstance):
            output.write(f"{space}dafnypy.ensures( ")
            expr2py(output, ens.condition)
            output.write(" )\n")


def decreases2py(output, decreases: dfy_s.Decreases, indent):
    space = "  " * indent
    for dec in decreases:
        output.write(f"{space}dafnypy.decreases( ")
        expr2py(output, dec.condition)
        output.write(" )\n")


def import_builder(module: Module):
    global IMPORTS

    def import_stmt(stmt: s.Statement):
        match stmt:
            case dfy_s.DeclAssignment(_, target, _, ty) if isinstance(
                target, e.Identifier
            ):
                import_type(ty)

            case s.If(_, _, body, orelse):
                import_stmt(body)
                import_stmt(orelse)
            case s.Block(_, stmts):
                for stmt in stmts:
                    import_stmt(stmt)
            case dfy_s.While(_, _, _, _, body):
                import_stmt(body)
            case _:
                return

    def import_type(type: t.Type):
        if isinstance(type, ListType):
            IMPORTS.add("List")
            import_type(type.element)

        if isinstance(type, SetType):
            IMPORTS.add("Set")
            import_type(type.element)

    for param in module.params.params:
        import_type(param.type)
    import_type(module.return_type)
    if module.method_or_function == "function":
        return
    for stmt in module.body.statements:
        import_stmt(stmt)


def import2py(output):
    for import_ in IMPORTS:
        output.write(f"from typing import {import_}\n")


def module2py(output, module: Module, indent, annotations=True, comments=True):
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


    output.write("@dafnypy.verify\n")
    if method_or_function == "method":
        output.write(f"def {name} ")
        params2dfy(output, module.params)
        output.write(" -> ")

        type2py(output, module.return_type)
        output.write(" :\n")

        # return_statement2dfy(output, )
        indent += 1
        if ANNOTATIONS:
            requires2py(output, module.requires, indent)
        for statement in module.body.statements:
            stmt2py(output, statement, indent)
        if ANNOTATIONS:    
            ensures2py(output, module.ensures, indent)
        final_return(output, indent)
        
    elif method_or_function == "function":
        output.write(f"def {name} ")
        params2dfy(output, module.params)
        output.write(" -> ")
        type2py(output, module.return_type)
        output.write(":\n")

        indent += 1
        if ANNOTATIONS:
            requires2py(output, module.requires, indent)
            ensures2py(output, module.ensures, indent)
        space = "  " * indent
        output.write(space + "return ")
        expr2py(output, module.body)
        output.write("\n")

    else:
        raise ValueError(
            f"Unsupported {method_or_function} is not a method or function"
        )

def modules2py(output, modules: List[Module], indent, annotations=True, comments=True):
    modules = [module for module in modules if module.position.unique >=0]
    
    output.write("import dafnypy\n")
    for module in modules: 
        import_builder(module)
    import2py(output)
    for module in modules:
        module2py(output, module, indent, annotations, comments)

def params2dfy(output, params: Params) -> str:
    output.write("(")

    for i, param in enumerate(params.params):
        param2dfy(output, param)
        if i < len(params) - 1:
            output.write(", ")
    output.write(")")


def param2dfy(output, param: Param) -> str:
    output.write(f"{param.name.name} :")
    type2py(output, param.type)
def final_return (output, indent):
    space = "  " * indent
    output.write(space + "return result\n")

def stmt2py(output, stmt: s.Statement, indent):
    space = "  " * indent
    match stmt:
        case s.Assignment(_, target, value) if isinstance(target, e.Identifier):
            target = target.name
            output.write(space + target)
            output.write(" = ")
            expr2py(output, value)
            output.write("\n")
        case s.Assignment(_, target, value) if isinstance(target, Hole):
            target = target.name
            output.write(space )
            output.write("?? = ")
            expr2py(output, value)
            output.write("\n")
        case dfy_s.DeclAssignment(_, target, value, ty) if isinstance(
            target, e.Identifier
        ):
            target = target.name

            output.write(space + f"{target} : ")
            type2py(output, ty)
            output.write(" = ")
            expr2py(output, value)
            output.write("\n")
        case dfy_s.DeclAssignment(_, target, value, ty) if isinstance(
            target, Hole
        ):
            target = target.name

            output.write(space + f"?? : ")
            type2py(output, ty)
            output.write(" = ")
            expr2py(output, value)
            output.write("\n")
        case s.If(_, cond, body, orelse):
            output.write(space)
            output.write("if (")
            expr2py(output, cond)
            output.write("): \n")
            stmt2py(output, body, indent + 1)
            if orelse.statements != []:
                output.write(space + "else: \n")
                stmt2py(output, orelse, indent + 1)
            output.write(space + "\n")
        case s.Skip(_):
            pass
        case s.Block(_, stmts):
            if stmts:
                for stmt in stmts:
                    stmt2py(output, stmt, indent)
            else:
                pass
        case s.Havoc(_, target):
            name = target.name
            output.write(space + name + " = ??" + "\n")
        case s.Assume(_, cond):
            output.write(space + "dafnypy.assume ")
            expr2py(output, cond)
            output.write("\n")
        case s.Assert(_, cond):
            output.write(space + "assert ")
            expr2py(output, cond)
            output.write("\n")
        case Hole(_):
            
            output.write(space + "??\n")
        case dfy_s.Return(_, value):
            output.write(space + "result = ")
            expr2py(output, value)
            output.write("\n")
        case dfy_s.Requires(_, cond):
            if ANNOTATIONS:
                output.write(space + "dafnypy.requires( ")
                expr2py(output, cond)
                output.write(")\n")

        case dfy_s.Ensures(_, cond):
            if ANNOTATIONS:
                output.write(space + "dafnypy.ensures( ")
                expr2py(output, cond)
                output.write(")\n")
        case dfy_s.While(_, cond, invariant, decreases, body):
            output.write(space + "while (")
            expr2py(output, cond)
            output.write("):\n")
            for inv in invariant:
                if ANNOTATIONS:
                    output.write(space + "  " + "dafnypy.invariant(")
                    expr2py(output, inv.condition)
                    output.write(")\n")
            for dec in decreases:
                if ANNOTATIONS:
                    output.write(space + "  " + "dafnypy.decreases(")
                    expr2py(output, dec.condition)
                    output.write(")\n")
            stmt2py(output, body, indent + 1)

        case dfy_s.Comment(_, comment):
            if COMMENTS:
                output.write(space + comment + "\n")
        case dfy_s.Append(_, lst, item):
            output.write(space)
            output.write(lst.name + ".append(")
        case dfy_s.Invariant(_, condition):
            if ANNOTATIONS:
                output.write(space + "dafnypy.invariant( ")
                expr2py(output, condition)
                output.write(")\n")
        case dfy_s.Decreases(_, condition):
            if ANNOTATIONS:
                output.write(space + "dafnypy.decreases( ")
                expr2py(output, condition)
                output.write(")\n")
        
        case _:
            import ipdb; ipdb.set_trace()
            output.write(space + "??\n")


def expr2py(output, expr: e.Expression):
    match expr:
        case e.Variant(_, name):
            output.write(name)
        case e.Selection(_, target, field):
            expr2py(output, target)
            output.write(".")
            output.write(field.name)
        case e.Application(_, name, args) if isinstance(name, e.Identifier):
            name = name.name

            output.write(name)
            if len(args) > 0:
                output.write("(")
                for i, a in enumerate(args):
                    if i > 0:
                        output.write(", ")
                    expr2py(output, a)
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
                        type2py(output, ty)
                    output.write(") :: ")
                    expr2py(output, args[0])
                    output.write(")")
                case e.Not(_):
                    op2py(output, op)
                    output.write("(")
                    expr2py(output, args[0])
                    output.write(")")
                case e.Add(_) | e.Subtract(_) | e.Multiply(_) | e.Divide(_) | e.Modulo(
                    _
                ) | e.And(_) | e.Or(_):
                    for i, a in enumerate(args):
                        if i > 0:
                            output.write(" ")
                            op2py(output, op)
                            output.write(" ")
                        expr2py(output, a)
                case e.Equal(_) | e.NotEqual(_) | e.LessThan(_) | e.GreaterThan(
                    _
                ) | e.LessThanOrEqual(_) | e.GreaterThanOrEqual(_):
                    expr2py(output, args[0])
                    for i, a in enumerate(args[1:]):
                        output.write(" ")
                        op2py(output, op)
                        output.write(" ")
                        expr2py(output, a)
                        if i < len(args) - 2:
                            output.write(" ")
                            op2py(output, e.And(op.position))
                            output.write(" ")
                            expr2py(output, args[i + 1])
                case dfy_e.In(_):
                    expr2py(output, args[0])
                    output.write(" in ")
                    expr2py(output, args[1])
                case dfy_e.Neg(_):
                    output.write("-")
                    expr2py(output, args[0])
                case dfy_e.Power(_):
                    output.write("(")
                    expr2py(output, args[0])
                    output.write(" ** ")
                    expr2py(output, args[1])
                    output.write(")")
                case e.Implies(_):
                    output.write("implies (")
                    expr2py(output, args[0])
                    output.write(", ")
                    expr2py(output, args[1])
                    output.write(")")
                case dfy_e.IntDivide(_):
                    expr2py(output, args[0])
                    output.write(" // ")
                    expr2py(output, args[1])

                case _:
                    output.write("??")
        case e.Boolean(_, value) | e.Integer(_, value):
            output.write(str(value).lower())
        case e.BitVector(_, value, width):
            output.write(f"{value}bv{width}")
        case Hole(_):
            output.write("??")
        case dfy_e.Subscript(_, list_value, subscript):
            expr2py(output, list_value)
            output.write("[")
            expr2py(output, subscript)
            output.write("]")
        case dfy_e.Slice(_, start, end, step):
            if start:
                expr2py(output, start)
            output.write(":")
            if end:
                expr2py(output, end)
            if step:
                print("step is currently not supported")
                # TODO: support reverse and maybe implement a built in
        case dfy_e.Ite(_, condition, then_expr, else_expr):
            expr2py(output, then_expr)
            output.write(" if ")
            expr2py(output, condition)
            output.write(" else ")
            expr2py(output, else_expr)
        case dfy_e.ForAll(_, variable, domain, predicate, condition):
            output.write("all(")
            expr2py(output, predicate)
            output.write(f" for {variable.name} in ")
            expr2py(output, domain)

            if condition is not None:
                output.write(" if ")
                expr2py(output, condition)
            output.write(")")

        case dfy_e.EmptyList(_):
            output.write("[]")

        case dfy_e.Set(_, content):
            if content is not None:
                output.write("{")
                for c in content:
                    expr2py(output, c)
                output.write("}")
            else:
                output.write("set()")

        case _:
            output.write("??")


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
