import eudoxus.ast.expression as e
import eudoxus.ast.proof as p
import eudoxus.ast.statement as s
import eudoxus.ast.type as t
from eudoxus.ast import node as n
from eudoxus.ast.module import Module


def module2py(output, module: Module, indent):
    name = module.name.name
    output.write(f"class {name}(Module):\n")
    indent += 1

    before = output.tell()

    types2py(output, module.types, indent)
    state2py(output, module.locals, indent, "locals")
    state2py(output, module.inputs, indent, "inputs")
    state2py(output, module.outputs, indent, "outputs")
    state2py(output, module.sharedvars, indent, "sharedvars")
    instances2py(output, module.instances, indent)
    init2py(output, module.init, indent)
    next2py(output, module.next, indent)
    specs2py(output, module.specification, indent)
    control2py(output, module.control, indent)

    # if we didn't write anything other than the class definition, write a hole
    after = output.tell()
    if before == after:
        output.write("  ??\n")


def types2py(output, types: s.Block, indent):
    match types:
        case s.Block(_, []):
            return
    space = "  " * indent
    output.write(f"{space}def types(self):\n")
    decl2py(output, types, indent + 1)
    output.write("\n")


def state2py(output, decls: s.Block, indent, kind):
    match decls:
        case s.Block(_, []):
            return
    space = "  " * indent
    output.write(f"{space}def {kind}(self):\n")
    decl2py(output, decls, indent + 1)
    output.write("\n")


def instances2py(output, instances: s.Block, indent):
    match instances:
        case s.Block(_, []):
            return
    space = "  " * indent
    output.write(f"{space}def instances(self):\n")
    decl2py(output, instances, indent + 1)
    output.write("\n")


def init2py(output, init: s.Block, indent):
    match init:
        case s.Block(_, []):
            return
    space = "  " * indent
    output.write(f"{space}def init(self):\n")
    stmt2py(output, init, indent + 1)
    output.write("\n")


def next2py(output, next: s.Block, indent):
    match next:
        case s.Block(_, []):
            return
    space = "  " * indent
    output.write(f"{space}def next(self):\n")
    stmt2py(output, next, indent + 1)
    output.write("\n")


def specs2py(output, spec: e.Expression, indent):
    match spec:
        case e.BooleanValue(_, True):
            return
    space = "  " * indent
    output.write(f"{space}def specification(self):\n")
    output.write(f"{space}  return ")
    expr2py(output, spec)
    output.write("\n\n")


def control2py(output, control: p.Command, indent):
    match control:
        case p.Block(_, []):
            return
    space = "  " * indent
    output.write(f"{space}def proof(self):\n")
    cmd2py(output, control, indent + 1)
    output.write("\n")


def decl2py(output, decl: s.Declaration, indent):
    space = "  " * indent
    match decl:
        case s.LocalDecl(_, name, type) | s.InputDecl(_, name, type) | s.OutputDecl(
            _, name, type
        ) | s.SharedDecl(_, name, type):
            name = name.name
            output.write(space + "self." + name)
            output.write(" = ")
            type2py(output, type)
            output.write("\n")
        case s.TypeDecl(_, name, type):
            name = name.name
            output.write(space + "self." + name)
            output.write(" = ")
            type2py(output, type)
            output.write("\n")
        case s.Block(_, decls):
            if decls:
                for decl in decls:
                    decl2py(output, decl, indent)
            else:
                output.write(f"{space}pass\n")
        case s.InstanceDecl(_, name, mod, args):
            name = name.name
            mod = mod.name
            output.write(space + "self." + name)
            output.write(" = ")
            output.write(mod)
            output.write("(")
            for i, (k, v) in enumerate(args):
                if i > 0:
                    output.write(", ")
                output.write(k.name)
                output.write("=")
                expr2py(output, v)
            output.write(")\n")
        case _:
            raise ValueError(f"Unsupported declaration {decl}")


def type2py(output, type: t.Type):
    match type:
        case t.BooleanType(_):
            output.write("bool")
        case t.IntegerType(_):
            output.write("int")
        case t.RealType(_):
            output.write("Real()")
        case t.BitVectorType(_, size):
            output.write(f"BitVector({size})")
        case t.ArrayType(_, inbdex_t, elem_t):
            output.write("Array(")
            type2py(output, inbdex_t)
            output.write(", ")
            type2py(output, elem_t)
            output.write(")")
        case t.EnumeratedType(_, values):
            output.write("Enum(")
            values = sorted(values, key=lambda v: v.name)
            for i, v in enumerate(values):
                if i > 0:
                    output.write(", ")
                if isinstance(v, n.HoleId):
                    output.write("??")
                else:
                    output.write('"')
                    output.write(v.name)
                    output.write('"')
            output.write(")")
        case t.RecordType(_, fields):
            output.write("Record(")
            for i, (k, v) in enumerate(fields):
                if i > 0:
                    output.write(", ")
                output.write("('")
                output.write(k.name)
                output.write("', ")
                type2py(output, v)
                output.write(")")
            output.write(")")
        case t.SynonymType(_, name):
            output.write("self." + name.name)
        case t.HoleType(_) | n.HoleId(_):
            output.write("??")
        case _:
            raise ValueError(f"Unsupported type {type}")


def expr2py(output, expr: e.Expression):
    match expr:
        case e.BooleanValue(_, value) | e.IntegerValue(_, value):
            output.write(repr(value))
        case e.RealValue(_, value):
            output.write(str(value))
        case e.BitVectorValue(_, value, width):
            output.write(f"BitVectorVal({value}, {width})")
        case e.EnumValue(_, value):
            output.write('"')
            output.write(value)
            output.write('"')
        case e.RecordSelect(_, target, field):
            expr2py(output, target)
            output.write(".")
            output.write(field.name)
        case e.InstanceSelect(_, target, field):
            output.write("self." + target.name)
            output.write(".")
            output.write(field.name)
        case e.ArraySelect(_, target, index):
            expr2py(output, target)
            output.write("[")
            expr2py(output, index)
            output.write("]")
        case e.ArrayStore(_, target, index, value):
            output.write("ArrayStore(")
            expr2py(output, target)
            output.write(", ")
            expr2py(output, index)
            output.write(", ")
            expr2py(output, value)
            output.write(")")
        case e.Ite(_, cond, then, else_):
            output.write("(")
            expr2py(output, then)
            output.write(" if ")
            expr2py(output, cond)
            output.write(" else ")
            expr2py(output, else_)
            output.write(")")
        case e.Add(_, lhs, rhs):
            output.write("(")
            expr2py(output, lhs)
            output.write(" + ")
            expr2py(output, rhs)
            output.write(")")
        case e.Subtract(_, lhs, rhs):
            output.write("(")
            expr2py(output, lhs)
            output.write(" - ")
            expr2py(output, rhs)
            output.write(")")
        case e.Negate(_, arg):
            output.write(" -")
            expr2py(output, arg)
        case e.Multiply(_, lhs, rhs):
            output.write("(")
            expr2py(output, lhs)
            output.write(" * ")
            expr2py(output, rhs)
            output.write(")")
        case e.Divide(_, lhs, rhs):
            output.write("(")
            expr2py(output, lhs)
            output.write(" / ")
            expr2py(output, rhs)
            output.write(")")
        case e.Modulo(_, lhs, rhs):
            output.write("(")
            expr2py(output, lhs)
            output.write(" % ")
            expr2py(output, rhs)
            output.write(")")
        case e.And(_, lhs, rhs):
            output.write("(")
            expr2py(output, lhs)
            output.write(" and ")
            expr2py(output, rhs)
            output.write(")")
        case e.Or(_, lhs, rhs):
            output.write("(")
            expr2py(output, lhs)
            output.write(" or ")
            expr2py(output, rhs)
            output.write(")")
        case e.Xor(_, lhs, rhs):
            output.write("Xor(")
            expr2py(output, lhs)
            output.write(", ")
            expr2py(output, rhs)
            output.write(")")
        case e.Not(_, target):
            output.write("not ")
            expr2py(output, target)
        case e.Implies(_, lhs, rhs):
            output.write("Implies(")
            expr2py(output, lhs)
            output.write(", ")
            expr2py(output, rhs)
            output.write(")")
        case e.Equal(_, lhs, rhs):
            output.write("(")
            expr2py(output, lhs)
            output.write(" == ")
            expr2py(output, rhs)
            output.write(")")
        case e.NotEqual(_, lhs, rhs):
            output.write("(")
            expr2py(output, lhs)
            output.write(" != ")
            expr2py(output, rhs)
            output.write(")")
        case e.LessThan(_, lhs, rhs):
            output.write("(")
            expr2py(output, lhs)
            output.write(" < ")
            expr2py(output, rhs)
            output.write(")")
        case e.LessThanOrEqual(_, lhs, rhs):
            output.write("(")
            expr2py(output, lhs)
            output.write(" <= ")
            expr2py(output, rhs)
            output.write(")")
        case e.GreaterThan(_, lhs, rhs):
            output.write("(")
            expr2py(output, lhs)
            output.write(" > ")
            expr2py(output, rhs)
            output.write(")")
        case e.GreaterThanOrEqual(_, lhs, rhs):
            output.write("(")
            expr2py(output, lhs)
            output.write(" >= ")
            expr2py(output, rhs)
            output.write(")")
        case e.Exists(_, x, t, body):
            output.write("Exists(")
            output.write("self." + x.name)
            output.write(", ")
            type2py(output, t)
            output.write(", ")
            expr2py(output, body)
            output.write(")")
        case e.Forall(_, x, t, body):
            output.write("Forall(")
            output.write("self." + x.name)
            output.write(", ")
            type2py(output, t)
            output.write(", ")
            expr2py(output, body)
            output.write(")")
        case e.FunctionApplication(_, f, args) if isinstance(f, e.Identifier):
            output.write("self." + f.name)
            if len(args) > 0:
                output.write("(")
                for i, a in enumerate(args):
                    if i > 0:
                        output.write(", ")
                    expr2py(output, a)
                output.write(")")
        case e.HoleExpr(_) | n.HoleId(_) | e.Nondet(_):
            output.write("??")
        case _:
            raise ValueError(f"Unsupported expression {expr}")


def stmt2py(output, stmt: s.Statement, indent):
    space = "  " * indent
    match stmt:
        case s.Assignment(
            _, target, e.ArrayStore(_, array, index, value)
        ) if array == target:
            output.write(space)
            expr2py(output, target)
            output.write("[")
            expr2py(output, index)
            output.write("]")
            output.write(" = ")
            expr2py(output, value)
            output.write("\n")
        case s.Assignment(_, target, value):
            output.write(space)
            expr2py(output, target)
            output.write(" = ")
            expr2py(output, value)
            output.write("\n")
        case s.If(_, cond, body, orelse):
            output.write(space)
            output.write("if ")
            expr2py(output, cond)
            output.write(":")
            output.write("\n")
            stmt2py(output, body, indent + 1)
            if orelse.statements != []:
                output.write(f"{space}else:\n")
                stmt2py(output, orelse, indent + 1)
        case s.Block(_, stmts):
            if stmts:
                for stmt in stmts:
                    stmt2py(output, stmt, indent)
            else:
                output.write(f"{space}??\n")
        case s.Havoc(_, target):
            name = target.name
            output.write(f"{space}Havoc(self.{name})\n")
        case s.Assume(_, cond):
            output.write(f"{space}Assume(")
            expr2py(output, cond)
            output.write(")\n")
        case s.Assert(_, cond):
            output.write(f"{space}assert ")
            expr2py(output, cond)
            output.write("\n")
        case s.Next(_, inst):
            output.write(f"{space}self.{inst.name}.next()\n")
        case s.HoleStmt(_):
            output.write(f"{space}??\n")
        case _:
            raise ValueError(f"Unsupported statement {stmt}")


def cmd2py(output, cmd: p.Command, indent):
    space = "  " * indent
    match cmd:
        case p.Block(_, cmds):
            if cmds:
                for cmd in cmds:
                    cmd2py(output, cmd, indent)
            else:
                output.write(f"{space}pass\n")
        case p.Induction(_, k):
            output.write(f"{space}self.induction({k})\n")
        case p.BoundedModelChecking(_, k):
            output.write(f"{space}self.bmc({k})\n")
        case p.HoleCmd(_):
            output.write(f"{space}??\n")
        case _:
            raise ValueError(f"Unsupported command {cmd}")
