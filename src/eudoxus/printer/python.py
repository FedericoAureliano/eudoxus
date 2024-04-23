import eudoxus.ast.expression as e
import eudoxus.ast.proof as p
import eudoxus.ast.statement as s
import eudoxus.ast.type as t
from eudoxus.ast.module import Module
from eudoxus.ast.node import Hole


def module2py(output, module: Module, indent):
    name = module.name.name
    output.write(f"class {name}(Module):\n")
    indent += 1

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
        case e.Boolean(_, True):
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
    output.write(f"{space}def control(self):\n")
    cmd2py(output, control, indent + 1)
    output.write("\n")


def decl2py(output, decl: s.Declaration, indent):
    space = "  " * indent
    match decl:
        case s.Variable(_, name, type):
            name = name.name
            output.write(space + "self." + name)
            output.write(" = ")
            type2py(output, type)
            output.write("\n")
        case s.Type(_, name, type):
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
        case s.Instance(_, name, mod, args):
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


def op2py(output, op: e.Operator):
    match op:
        case e.Or(_):
            output.write("or")
        case e.And(_):
            output.write("and")
        case e.Not(_):
            output.write("not")
        case e.Equal(_):
            output.write("==")
        case e.NotEqual(_):
            output.write("!=")
        case e.LessThan(_):
            output.write("<")
        case e.GreaterThan(_):
            output.write(">")
        case e.GreaterThanOrEqual(_):
            output.write(">=")
        case e.LessThanOrEqual(_):
            output.write("<=")
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
            output.write("Forall")
        case e.Exists(_):
            output.write("Exists")
        case _:
            raise ValueError(f"Unsupported operator {op}")


def type2py(output, type: t.Type):
    match type:
        case t.Boolean(_):
            output.write("bool")
        case t.Integer(_):
            output.write("int")
        case t.Float(_):
            output.write("float")
        case t.BitVector(_, size):
            output.write(f"BitVector({size})")
        case t.Array(_, inbdex_t, elem_t):
            output.write("Array(")
            type2py(output, inbdex_t)
            output.write(", ")
            type2py(output, elem_t)
            output.write(")")
        case t.Enumeration(_, values):
            output.write("Enum(")
            for i, v in enumerate(values):
                if i > 0:
                    output.write(", ")
                output.write('"')
                output.write(v.name)
                output.write('"')
            output.write(")")
        case t.Synonym(_, name):
            name = name.name
            output.write("self." + name)
        case Hole(_):
            output.write("??")
        case _:
            raise ValueError(f"Unsupported type {type}")


def expr2py(output, expr: e.Expression):
    match expr:
        case e.Variant(_, name):
            output.write('"' + name + '"')
        case e.Select(_, target, field):
            expr2py(output, target)
            output.write(".")
            output.write(field.name)
        case e.Index(_, target, index):
            expr2py(output, target)
            output.write("[")
            expr2py(output, index)
            output.write("]")
        case e.Application(_, f, args) if isinstance(f, e.Identifier):
            output.write("self." + f.name)
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
                    if isinstance(op, e.Forall):
                        output.write("Forall([")
                    else:
                        output.write("Exists([")
                    for i, (n, ty) in enumerate(bindings):
                        if i > 0:
                            output.write(", ")
                        output.write("(self.")
                        output.write(n.name)
                        output.write(", ")
                        type2py(output, ty)
                        output.write(")")
                    output.write("], ")
                    expr2py(output, args[0])
                    output.write(")")
                case e.Not(_):
                    op2py(output, op)
                    output.write(" ")
                    expr2py(output, args[0])
                case e.Ite(_):
                    expr2py(output, args[1])
                    output.write(" if ")
                    expr2py(output, args[0])
                    output.write(" else ")
                    expr2py(output, args[2])
                case _:
                    for i, a in enumerate(args):
                        if i > 0:
                            output.write(" ")
                            op2py(output, op)
                            output.write(" ")
                        expr2py(output, a)
        case e.Boolean(_, value) | e.Integer(_, value):
            output.write(repr(value))
        case e.BitVector(_, value, width):
            output.write(f"BitVectorVal({value}, {width})")
        case Hole(_):
            output.write("??")
        case _:
            raise ValueError(f"Unsupported expression {expr}")


def stmt2py(output, stmt: s.Statement, indent):
    space = "  " * indent
    match stmt:
        case s.Assignment(
            _, target, e.Store(_, array, index, value)
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
        case s.Skip(_):
            output.write(f"{space}pass\n")
        case s.Block(_, stmts):
            if stmts:
                for stmt in stmts:
                    stmt2py(output, stmt, indent)
            else:
                output.write(f"{space}pass\n")
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
        case _:
            raise ValueError(f"Unsupported command {cmd}")
