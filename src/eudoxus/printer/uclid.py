import eudoxus.ast.expression as e
import eudoxus.ast.proof as p
import eudoxus.ast.statement as s
import eudoxus.ast.type as t
from eudoxus.ast.module import Module
from eudoxus.ast.node import Hole


def module2ucl(output, module: Module, indent):
    name = module.name.name
    output.write(f"module {name} {{\n")
    indent += 1

    types2ucl(output, module.types, indent)
    state2ucl(output, module.locals, indent)
    state2ucl(output, module.inputs, indent)
    state2ucl(output, module.outputs, indent)
    state2ucl(output, module.sharedvars, indent)
    instance2ucl(output, module.instances, indent)
    init2ucl(output, module.init, indent)
    next2ucl(output, module.next, indent)
    specs2ucl(output, module.specification, indent)
    control2ucl(output, module.control, indent)

    output.write("}\n")


def types2ucl(output, types: s.Block, indent):
    match types:
        case s.Block(_, []):
            return
    decl2ucl(output, types, indent)
    output.write("\n")


def state2ucl(output, locals: s.Block, indent):
    match locals:
        case s.Block(_, []):
            return
    decl2ucl(output, locals, indent)
    output.write("\n")


def instance2ucl(output, instances: s.Block, indent):
    match instances:
        case s.Block(_, []):
            return
    decl2ucl(output, instances, indent)
    output.write("\n")


def init2ucl(output, init: s.Block, indent):
    match init:
        case s.Block(_, []):
            return
    space = "  " * indent
    output.write(space + "init {\n")
    stmt2ucl(output, init, indent + 1, False)
    output.write("\n")
    output.write(space + "}\n")


def next2ucl(output, next: s.Block, indent):
    match next:
        case s.Block(_, []):
            return
    space = "  " * indent
    output.write(space + "next {\n")
    stmt2ucl(output, next, indent + 1, True)
    output.write("\n")
    output.write(space + "}\n")


def specs2ucl(output, spec: e.Expression, indent):
    match spec:
        case e.Boolean(_, True):
            return
    space = "  " * indent
    output.write(f"{space}invariant spec: ")
    expr2ucl(output, spec)
    output.write(";\n\n")


def control2ucl(output, control: p.Command, indent):
    match control:
        case p.Block(_, []):
            return
    space = "  " * indent
    output.write(space + "control {\n")
    cmd2ucl(output, control, indent + 1)
    output.write("\n")
    output.write(space + "}\n")


def decl2ucl(output, decl: s.Declaration, indent):
    space = "  " * indent
    match decl:
        case s.Variable(_, name, type):
            name = name.name
            if isinstance(decl, s.Local):
                output.write(space + "var " + name)
            elif isinstance(decl, s.Input):
                output.write(space + "input " + name)
            elif isinstance(decl, s.Output):
                output.write(space + "output " + name)
            elif isinstance(decl, s.SharedVar):
                output.write(space + "sharedvar " + name)
            elif isinstance(decl, s.Constant):
                output.write(space + "const " + name)
            else:
                raise ValueError(f"Unsupported variable declaration {decl}")
            output.write(": ")
            type2ucl(output, type)
            output.write(";\n")
        case s.Type(_, name, type):
            name = name.name
            output.write(space + "type " + name)
            output.write(" = ")
            type2ucl(output, type)
            output.write(";\n")
        case s.Block(_, decls):
            for decl in decls:
                decl2ucl(output, decl, indent)
        case s.Instance(_, name, module, args):
            name = name.name
            mod = module.name
            output.write(space + "instance " + name + ": " + mod)
            output.write("(")
            for i, (k, v) in enumerate(args):
                if i > 0:
                    output.write(", ")
                output.write(k.name)
                output.write(":(")
                expr2ucl(output, v)
                output.write(")")
            output.write(");\n")
        case _:
            raise ValueError(f"Unsupported declaration {decl}")


def type2ucl(output, type: t.Type):
    match type:
        case t.Boolean(_):
            output.write("boolean")
        case t.Integer(_):
            output.write("integer")
        case t.Float(_):
            output.write("float")
        case t.BitVector(_, size):
            output.write(f"bv{size}")
        case t.Array(_, inbdex_t, elem_t):
            output.write("[")
            type2ucl(output, inbdex_t)
            output.write("]")
            type2ucl(output, elem_t)
        case t.Enumeration(_, values):
            output.write("enum { ")
            for i, v in enumerate(values):
                if i > 0:
                    output.write(", ")
                output.write(v.name)
            output.write(" }")
        case t.Synonym(_, name):
            name = name.name
            output.write(name)
        case Hole(_):
            output.write("??")
        case _:
            raise ValueError(f"Unsupported type {type}")


def op2ucl(output, op: e.Operator):
    match op:
        case e.Or(_):
            output.write("||")
        case e.And(_):
            output.write("&&")
        case e.Not(_):
            output.write("!")
        case e.Equal(_):
            output.write("==")
        case e.NotEqual(_):
            output.write("!=")
        case e.LessThan(_):
            output.write("<")
        case e.GreaterThan(_):
            output.write(">")
        case e.LessThanOrEqual(_):
            output.write("<=")
        case e.GreaterThanOrEqual(_):
            output.write(">=")
        case e.Add(_):
            output.write("+")
        case e.Subtract(_):
            output.write("-")
        case e.Multiply(_):
            output.write("*")
        case e.Divide(_):
            output.write("/")
        case e.Modulo(_):
            output.write("%")
        case e.Forall(_):
            output.write("forall")
        case e.Exists(_):
            output.write("exists")
        case _:
            raise ValueError(f"Unsupported operator {op}")


def expr2ucl(output, expr: e.Expression):
    match expr:
        case e.Variant(_, name):
            output.write(name)
        case e.Select(_, target, field):
            expr2ucl(output, target)
            output.write(".")
            output.write(field.name)
        case e.Index(_, target, index):
            expr2ucl(output, target)
            output.write("[")
            expr2ucl(output, index)
            output.write("]")
        case e.Store(_, target, index, value):
            expr2ucl(output, target)
            output.write("[")
            expr2ucl(output, index)
            output.write(" -> ")
            expr2ucl(output, value)
            output.write("]")
        case e.Application(_, name, args) if isinstance(name, e.Identifier):
            name = name.name
            output.write(name)
            if len(args) > 0:
                output.write("(")
                for i, a in enumerate(args):
                    if i > 0:
                        output.write(", ")
                    expr2ucl(output, a)
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
                        type2ucl(output, ty)
                    output.write(") :: ")
                    expr2ucl(output, args[0])
                    output.write(")")
                case e.Not(_):
                    op2ucl(output, op)
                    expr2ucl(output, args[0])
                case e.Add(_) | e.Subtract(_) | e.Multiply(_) | e.Divide(_) | e.Modulo(
                    _
                ) | e.And(_) | e.Or(_):
                    for i, a in enumerate(args):
                        if i > 0:
                            output.write(" ")
                            op2ucl(output, op)
                            output.write(" ")
                        expr2ucl(output, a)
                case e.Equal(_) | e.NotEqual(_) | e.LessThan(_) | e.GreaterThan(
                    _
                ) | e.LessThanOrEqual(_) | e.GreaterThanOrEqual(_):
                    expr2ucl(output, args[0])
                    for i, a in enumerate(args[1:]):
                        output.write(" ")
                        op2ucl(output, op)
                        output.write(" ")
                        expr2ucl(output, a)
                        if i < len(args) - 2:
                            output.write(" ")
                            op2ucl(output, e.And(op.position))
                            output.write(" ")
                            expr2ucl(output, args[i + 1])
                case e.Ite(_):
                    output.write("if (")
                    expr2ucl(output, args[0])
                    output.write(") then ")
                    expr2ucl(output, args[1])
                    output.write(" else ")
                    expr2ucl(output, args[2])
                case _:
                    raise ValueError(f"Unsupported operator {op}")
        case e.Boolean(_, value) | e.Integer(_, value):
            output.write(str(value).lower())
        case e.BitVector(_, value, width):
            output.write(f"{value}bv{width}")
        case Hole(_):
            output.write("??")
        case _:
            raise ValueError(f"Unsupported expression {expr}")


def stmt2ucl(output, stmt: s.Statement, indent, prime_assignments):
    space = "  " * indent
    match stmt:
        case s.Assignment(_, target, value):
            output.write(space)
            expr2ucl(output, target)
            if prime_assignments:
                output.write("'")
            output.write(" = ")
            expr2ucl(output, value)
            output.write(";\n")
        case s.If(_, cond, body, orelse):
            output.write(space)
            output.write("if (")
            expr2ucl(output, cond)
            output.write(") {\n")
            stmt2ucl(output, body, indent + 1, prime_assignments)
            if orelse.statements != []:
                output.write(space + "} else {\n")
                stmt2ucl(output, orelse, indent + 1, prime_assignments)
            output.write(space + "}\n")
        case s.Skip(_):
            pass
        case s.Block(_, stmts):
            if stmts:
                for stmt in stmts:
                    stmt2ucl(output, stmt, indent, prime_assignments)
            else:
                pass
        case s.Havoc(_, target):
            name = target.name
            output.write(space + "havoc " + name + ";\n")
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
