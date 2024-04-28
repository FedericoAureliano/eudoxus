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
        case e.BooleanValue(_, True):
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
        case s.LocalDecl(_, name, type):
            name = name.name
            output.write(space + "var " + name)
            output.write(": ")
            type2ucl(output, type)
            output.write(";\n")
        case s.InputDecl(_, name, type):
            name = name.name
            output.write(space + "input " + name)
            output.write(": ")
            type2ucl(output, type)
            output.write(";\n")
        case s.OutputDecl(_, name, type):
            name = name.name
            output.write(space + "output " + name)
            output.write(": ")
            type2ucl(output, type)
            output.write(";\n")
        case s.SharedDecl(_, name, type):
            name = name.name
            output.write(space + "sharedvar " + name)
            output.write(": ")
            type2ucl(output, type)
            output.write(";\n")
        case s.TypeDecl(_, name, type):
            name = name.name
            output.write(space + "type " + name)
            output.write(" = ")
            type2ucl(output, type)
            output.write(";\n")
        case s.Block(_, decls):
            for decl in decls:
                decl2ucl(output, decl, indent)
        case s.InstanceDecl(_, name, module, args):
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
        case Hole(_):
            output.write(space + "??;\n")
        case _:
            raise ValueError(f"Unsupported declaration {decl}")


def type2ucl(output, type: t.Type):
    match type:
        case t.BooleanType(_):
            output.write("boolean")
        case t.IntegerType(_):
            output.write("integer")
        case t.BitVectorType(_, size):
            output.write(f"bv{size}")
        case t.ArrayType(_, inbdex_t, elem_t):
            output.write("[")
            type2ucl(output, inbdex_t)
            output.write("]")
            type2ucl(output, elem_t)
        case t.EnumeratedType(_, values):
            output.write("enum { ")
            for i, v in enumerate(values):
                if i > 0:
                    output.write(", ")
                output.write(v.name)
            output.write(" }")
        case t.SynonymType(_, name):
            name = name.name
            output.write(name)
        case Hole(_):
            output.write("??")
        case _:
            raise ValueError(f"Unsupported type {type}")


def expr2ucl(output, expr: e.Expression):
    match expr:
        case e.BooleanValue(_, value) | e.IntegerValue(_, value):
            output.write(str(value).lower())
        case e.BitVectorValue(_, value, width):
            output.write(f"{value}bv{width}")
        case e.EnumValue(_, value):
            output.write(value)
        case e.RecordSelect(_, target, field):
            expr2ucl(output, target)
            output.write(".")
            output.write(field.name)
        case e.ArraySelect(_, target, index):
            expr2ucl(output, target)
            output.write("[")
            expr2ucl(output, index)
            output.write("]")
        case e.ArrayStore(_, target, index, value):
            expr2ucl(output, target)
            output.write("[")
            expr2ucl(output, index)
            output.write(" -> ")
            expr2ucl(output, value)
            output.write("]")
        case e.Ite(_, cond, then, else_):
            output.write("if ")
            expr2ucl(output, cond)
            output.write(" then ")
            expr2ucl(output, then)
            output.write(" else ")
            expr2ucl(output, else_)
        case e.Add(_, lhs, rhs):
            expr2ucl(output, lhs)
            output.write(" + ")
            expr2ucl(output, rhs)
        case e.Subtract(_, lhs, rhs):
            expr2ucl(output, lhs)
            output.write(" - ")
            expr2ucl(output, rhs)
        case e.Multiply(_, lhs, rhs):
            expr2ucl(output, lhs)
            output.write(" * ")
            expr2ucl(output, rhs)
        case e.Divide(_, lhs, rhs):
            expr2ucl(output, lhs)
            output.write(" / ")
            expr2ucl(output, rhs)
        case e.And(_, lhs, rhs):
            expr2ucl(output, lhs)
            output.write(" && ")
            expr2ucl(output, rhs)
        case e.Or(_, lhs, rhs):
            expr2ucl(output, lhs)
            output.write(" || ")
            expr2ucl(output, rhs)
        case e.Not(_, target):
            output.write("!")
            expr2ucl(output, target)
        case e.Equal(_, lhs, rhs):
            expr2ucl(output, lhs)
            output.write(" == ")
            expr2ucl(output, rhs)
        case e.NotEqual(_, lhs, rhs):
            expr2ucl(output, lhs)
            output.write(" != ")
            expr2ucl(output, rhs)
        case e.LessThan(_, lhs, rhs):
            expr2ucl(output, lhs)
            output.write(" < ")
            expr2ucl(output, rhs)
        case e.LessThanOrEqual(_, lhs, rhs):
            expr2ucl(output, lhs)
            output.write(" <= ")
            expr2ucl(output, rhs)
        case e.GreaterThan(_, lhs, rhs):
            expr2ucl(output, lhs)
            output.write(" > ")
            expr2ucl(output, rhs)
        case e.GreaterThanOrEqual(_, lhs, rhs):
            expr2ucl(output, lhs)
            output.write(" >= ")
            expr2ucl(output, rhs)
        case e.Exists(_, x, t, body):
            output.write("(exists (")
            output.write(x.name)
            output.write(":")
            type2ucl(output, t)
            output.write(") :: ")
            expr2ucl(output, body)
            output.write(")")
        case e.Forall(_, x, t, body):
            output.write("(forall (")
            output.write(x.name)
            output.write(":")
            type2ucl(output, t)
            output.write(") :: ")
            expr2ucl(output, body)
            output.write(")")
        case e.FunctionApplication(_, name, args) if isinstance(name, e.Identifier):
            name = name.name
            output.write(name)
            if len(args) > 0:
                output.write("(")
                for i, a in enumerate(args):
                    if i > 0:
                        output.write(", ")
                    expr2ucl(output, a)
                output.write(")")
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
