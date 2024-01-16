import ast
from _ast import (
    Assert,
    Assign,
    Attribute,
    AugAssign,
    BinOp,
    BoolOp,
    Call,
    Compare,
    Constant,
    Expr,
    FunctionDef,
    If,
    Lambda,
    Name,
    Pass,
    UnaryOp,
    With,
)

from . import control as control
from . import expr as expr
from . import types as types
from .control import *  # noqa: F401, F403
from .expr import *  # noqa: F401, F403
from .types import *  # noqa: F401, F403
from .utils import dump, generator_log, infer_type

control_dict = control.__dict__
expr_dict = expr.__dict__
types_dict = types.__dict__

operator_dict = {
    "Add": "+",
    "Sub": "-",
    "Mult": "*",
    "Div": "/",
    "Mod": "%",
    "LShift": "<<",
    "RShift": ">>",
    "BitOr": "|",
    "BitXor": "^",
    "BitAnd": "&",
    "Eq": "==",
    "NotEq": "!=",
    "Lt": "<",
    "LtE": "<=",
    "Gt": ">",
    "GtE": ">=",
    "And": "&&",
    "Or": "||",
    "Not": "!",
    "UAdd": "+",
    "USub": "-",
    "Pow": "^",
    "In": "??",
}


class UclidPrinter(ast.NodeVisitor):
    def __init__(self) -> None:
        super().__init__()
        self.should_prime = False

    def visit(self, node) -> str:
        out = super().visit(node)
        if out is None:
            generator_log(f'`visit` will return "" on {dump(node)}')
            return ""
        return out

    def visit_Module(self, node) -> str:
        """A Python Module is a UCLID5 file."""
        return "\n".join(map(self.visit_toplevel, node.body))

    def visit_ClassDef(self, node) -> str:
        """A Python Class is a UCLID5 module."""
        body = "\n".join(map(self.visit_toplevel, node.body))
        if body:
            body = "\n" + body + "\n"
        return f"module {node.name} {{{body}}}"

    def visit_Pass(self, _: Pass) -> str:
        """A Python Pass is a UCLID5 empty statement."""
        return ""

    def visit_FunctionDef(self, node: FunctionDef) -> str:
        """A Python Function can be a few things in UCLID5:
        - state is where we declare variables
        - next is the transition relation
        - init is the initialization steps
        - specification holds all the invariants
        - proof is the control block
        """
        match node.name:
            case "types":
                return self.visit_types(node)
            case "state":
                return self.visit_state(node)
            case "inputs":
                return self.visit_inputs(node)
            case "outputs":
                return self.visit_outputs(node)
            case "instances":
                return self.visit_instances(node)
            case f if f.startswith("next") or f in ["transition", "next_state"]:
                return self.visit_next(node)
            case f if f.startswith("init") or f in ["initialization", "init_state"]:
                return self.visit_init(node)
            case f if f in ["specification", "invariant", "invariants", "spec"]:
                return self.visit_specification(node)
            case f if f in ["proof", "control"]:
                return self.visit_proof(node)
            case _:
                generator_log(f'`visit_FunctionDef` will return "" on {dump(node)}.')
                return ""

    def visit_types(self, node: FunctionDef) -> str:
        """
        Python types is where types are declared.
        """
        body = node.body
        return "\n".join(map(self.visit_type_decls, body)) + "\n"

    def visit_state(self, node: FunctionDef) -> str:
        """
        Python state function is where variables are declared.
        """
        body = node.body
        return "\n".join(map(lambda x: self.visit_decl(x, "var"), body)) + "\n"

    def visit_inputs(self, node: FunctionDef) -> str:
        """
        Python inputs function is where input variables are declared.
        """
        body = node.body
        return "\n".join(map(lambda x: self.visit_decl(x, "input"), body)) + "\n"

    def visit_outputs(self, node: FunctionDef) -> str:
        """
        Python outputs function is where output variables are declared.
        """
        body = node.body
        return "\n".join(map(lambda x: self.visit_decl(x, "output"), body)) + "\n"

    def visit_instances(self, node: FunctionDef) -> str:
        """
        Python instances function is where modules are instantiated.
        """
        body = node.body
        return "\n".join(map(self.visit_instance_decl, body)) + "\n"

    def visit_type_decls(self, node) -> str:
        """A Python declaration is a UCLID5 type declaration."""
        match node:
            case ast.Assign(targets, value, _):
                target = self.visit(targets[0])
                value = self.visit(value)
                value = infer_type(value)
                return f"type {target} = {value};"
            case ast.Expr(ast.Constant(_)):
                return self.visit_comment(node.value)
            case _:
                generator_log(f'`visit_type_decls` will return "" on {dump(node)}.')
                return ""

    def visit_decl(self, node, kind) -> str:
        """A Python declaration is a UCLID5 variable declaration."""
        match node:
            case ast.Assign(targets, value, _):
                target = self.visit(targets[0])
                value = self.visit(value)
                value = infer_type(value)
                return f"{kind} {target} : {value};"
            case ast.Expr(ast.Constant(_)):
                return self.visit_comment(node.value)
            case _:
                generator_log(f'`visit_decl` will return "" on {dump(node)}.')
                return ""

    def visit_instance_decl(self, node) -> str:
        """A Python instance declaration is a UCLID5 instance declaration."""
        match node:
            case ast.Assign(targets, value, _):
                target = self.visit(targets[0])
                match value:
                    case ast.Call(func, args, keywords):
                        args = []
                        for keyword in keywords:
                            args.append(
                                f"{keyword.arg} : ({self.visit(keyword.value)})"
                            )
                        args = ", ".join(args)
                        return f"instance {target} : {func.id}({args});"
                    case _:
                        generator_log(
                            f'`visit_instance_decl` will return "??" on {dump(value)}.'
                        )
                        return f"instance {target} : ??;"
            case ast.Expr(ast.Constant(_)):
                return self.visit_comment(node.value)
            case _:
                generator_log(f'`visit_isntance_decl` will return "" on {dump(node)}.')
                return ""

    def visit_next(self, node: FunctionDef) -> str:
        """
        next is the UCLID5 transition relation.
        """
        self.should_prime = True
        body = "\n".join(map(self.visit_statements, node.body))
        self.should_prime = False
        if body:
            body = "\n" + body + "\n"
        return f"next {{{body}}}"

    def visit_init(self, node: FunctionDef) -> str:
        """
        init is the UCLID5 initialization block.
        """
        body = "\n".join(map(self.visit_statements, node.body))
        if body:
            body = "\n" + body + "\n"
        return f"init {{{body}}}"

    def visit_proof(self, node: FunctionDef) -> str:
        """
        proof is the UCLID5 control block.
        """
        body = "\n".join(map(self.visit_control_cmds, node.body))
        if body:
            body = "\n" + body + "\n"
        return f"control {{{body}}}"

    def visit_control_cmds(self, node) -> str:
        """UCLID5 control commands are Python function calls, but a small subset."""
        match node:
            case ast.Expr(ast.Call(func, _, _)) if self.visit(func) in control_dict:
                return self.visit(node)
            case ast.Expr(ast.Constant(_)):
                return self.visit_comment(node.value)
            case _:
                generator_log(f'`visit_control_cmds` will return "" on {dump(node)}.')
                return ""

    def visit_statements(self, node) -> str:
        """A Python statement is a UCLID5 statement."""
        match node:
            case ast.Expr(ast.Constant(_)):
                return self.visit_comment(node.value)
            case _:
                return self.visit(node)

    def visit_toplevel(self, node) -> str:
        """These are comments, type declarations, variable declarations, etc..."""
        match node:
            case ast.Expr(ast.Constant(_)):
                return self.visit_comment(node.value)
            case _:
                return self.visit(node)

    def visit_specification(self, node: FunctionDef) -> str:
        """A Python specification is a function that returns a boolean."""
        body = node.body
        match body:
            case [ast.Return(value)]:
                value = self.visit(value)
                return f"invariant spec: {value};"
            case [ast.Expr(ast.Constant(_)), ast.Return(value)]:
                comment = self.visit_comment(body[0].value)
                value = self.visit(value)
                return f"{comment}invariant spec: {value};"
            case _:
                generator_log(f'`visit_specification` will return "" on {dump(node)}')
                return ""

    def visit_Assign(self, node: Assign) -> str:
        """A Python assignment is a UCLID5 assignment."""
        target = self.visit(node.targets[0])
        if self.should_prime:
            target = f"{target}'"
        value = self.visit(node.value)
        return f"{target} = {value};"

    def visit_Attribute(self, node: Attribute) -> str:
        """A Python Attribute is a UCLID5 field access
        or, if the attribute is self, then it is ignored.
        """
        value = self.visit(node.value)
        attr = node.attr
        if value == "self":
            return attr
        return f"{value}.{attr}"

    def visit_Name(self, node: Name) -> str:
        """A Python Name is a UCLID5 name"""
        return node.id

    def visit_Call(self, node: Call) -> str:
        """A Python Call can be a few things in UCLID5:
        - a function call
        - a procedure call
        - a type constructor
        - or just a Python call that we want to execute
        """
        match node.func:
            case Attribute(value, attr) if self.visit(value) == "self" and len(
                node.args
            ) == 0:
                return attr
            case Attribute(value, attr) if attr == "next":
                return f"{attr}({self.visit(value)});"
            case func if self.visit(func) in expr_dict | types_dict | control_dict:
                func = self.visit(func)
                args = ", ".join(
                    map(lambda arg: self.quote(self.visit(arg)), node.args)
                )
                keyword_args = ", ".join(
                    map(
                        lambda k: f"{k.arg}={self.quote(self.visit(k.value))}",
                        node.keywords,
                    )
                )
                if args and keyword_args:
                    args += ", " + keyword_args
                elif keyword_args:
                    args = keyword_args
                to_eval = f"{func}({args})"
                generator_log(f"About to eval `{to_eval}`")
                return eval(to_eval)
            case _:
                generator_log(
                    f':warning: `visit_Call` will return "??" on {dump(node)}.'
                )
                return "??"

    def quote(self, x: str) -> str:
        """A Python string is a UCLID5 string"""
        if not x.startswith('"') and not x.startswith("'"):
            return f'"{x}"'
        return x

    def visit_Constant(self, node: Constant) -> str:
        """A Python constant is a UCLID5 literal"""
        if isinstance(node.value, str):
            return self.quote(node.value)
        if isinstance(node.value, bool):
            return str(node.value).lower()
        return str(node.value)

    def visit_comment(self, node: Constant) -> str:
        """A Python comment is a UCLID5 comment"""
        comment = node.value.split("\n")
        comment = "\n".join(map(lambda line: f"// {line}", comment))
        return f"{comment}\n"

    def visit_BinOp(self, node: BinOp) -> str:
        """A Python binary operation is a UCLID5 binary operation"""
        left = self.visit(node.left)
        right = self.visit(node.right)
        op = node.op
        if op.__class__.__name__ in operator_dict:
            op = operator_dict[op.__class__.__name__]
        else:
            generator_log(f'`visit_BinOp` will return "" on {dump(node)}.')
            return ""
        return f"{left} {op} {right}"

    def visit_BoolOp(self, node: BoolOp) -> str:
        """A Python boolean operation is a UCLID5 boolean operation"""
        values = node.values
        op = node.op
        if op.__class__.__name__ in operator_dict:
            op = operator_dict[op.__class__.__name__]
        else:
            generator_log(f'`visit_BoolOp` will return "" on {dump(node)}.')
            return ""
        return f" {op} ".join(map(self.visit, values))

    def visit_UnaryOp(self, node: UnaryOp) -> str:
        """A Python unary operation is a UCLID5 unary operation"""
        operand = self.visit(node.operand)
        op = node.op
        if op.__class__.__name__ in operator_dict:
            op = operator_dict[op.__class__.__name__]
        else:
            generator_log(f'`visit_UnaryOp` will return "" on {dump(node)}.')
            return ""
        return f"{op} {operand}"

    def visit_Compare(self, node: Compare) -> str:
        """A Python comparison is a UCLID5 comparison"""
        ops = list(map(lambda op: operator_dict[op.__class__.__name__], node.ops))
        args = [self.visit(node.left)] + list(map(self.visit, node.comparators))
        outputs = []
        for i in range(len(args) - 1):
            outputs.append(f"{args[i]} {ops[i]} {args[i + 1]}")
        return " && ".join(outputs)

    def visit_Expr(self, node: Expr) -> str:
        """A Python expression is just a wrapper, so descend into the value."""
        return self.visit(node.value)

    def visit_Subscript(self, node) -> str:
        """A Python subscript is a UCLID5 array access."""
        value = self.visit(node.value)
        slice = self.visit(node.slice)
        return f"{value}[{slice}]"

    def visit_If(self, node: If) -> str:
        """A Python if statement is a UCLID5 if statement."""
        test = self.visit(node.test)
        body = "\n".join(map(self.visit, node.body))
        orelse = "\n".join(map(self.visit, node.orelse))

        if orelse:
            return f"if ({test}) {{\n{body}\n}} else {{\n{orelse}\n}}\n"
        else:
            return f"if ({test}) {{\n{body}\n}}\n"

    def visit_IfExp(self, node) -> str:
        """A Python if expression is a UCLID5 if expression."""
        test = self.visit(node.test)
        body = self.visit(node.body)
        orelse = self.visit(node.orelse)
        return expr.Ite(test, body, orelse)

    def visit_AugAssign(self, node: AugAssign) -> str:
        """A Python AugAssign is a UCLID5 assignment with an addition"""
        target = self.visit(node.target)
        if self.should_prime:
            target_lhs = f"{target}'"
        else:
            target_lhs = target
        value = self.visit(node.value)
        op = node.op
        if op.__class__.__name__ in operator_dict:
            op = operator_dict[op.__class__.__name__]
        else:
            generator_log(f'`visit_AugAssing` will return "" on {dump(node)}.')
            return ""
        return f"{target_lhs} = {target} {op} {value};"

    def visit_With(self, node: With):
        """With statements are ignored."""
        generator_log(
            f"`visit_With` will give an unkown guard for the body of {dump(node)}."
        )
        body = "\n".join(map(self.visit, node.body))
        body = "if (??) {\n" + body + "\n}\n"
        return body

    def visit_Lambda(self, node: Lambda):
        """Lambda expressions are array constructors."""
        if len(node.args.args) != 1 and node.args.args[0].arg != "_":
            generator_log(f':warning: `visit_Lambda` will return "??" on {dump(node)}.')
            return "??"
        body = self.visit(node.body)
        return f"const({body})"

    def visit_Assert(self, node: Assert):
        """Python assert statements are assert statements in UCLID5."""
        test = self.visit(node.test)
        return f"assert({test});"


def print_uclid5(node) -> str:
    """Print a UCLID5 expression."""
    return UclidPrinter().visit(node)
