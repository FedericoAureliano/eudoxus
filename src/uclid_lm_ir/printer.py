import ast
from _ast import (
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
from .utils import Kind, dump, infer_type, log

support_dict = control.__dict__ | types.__dict__ | expr.__dict__

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
}


class UclidPrinter(ast.NodeVisitor):
    def __init__(self) -> None:
        super().__init__()
        self.should_prime = False

    def visit(self, node) -> str:
        out = super().visit(node)
        if out is None:
            log(
                f'`visit` will return "" on {dump(node)}',
                Kind.WARNING,
            )
            return ""
        return out

    def visit_Module(self, node) -> str:
        """A Python Module is a UCLID5 file."""
        return "\n".join(map(self.visit, node.body))

    def visit_ClassDef(self, node) -> str:
        """A Python Class is a UCLID5 module."""
        body = "\n".join(map(self.visit, node.body))
        if body:
            body = "\n" + body + "\n"
        return f"module {node.name} {{{body}}}"

    def visit_Pass(self, _: Pass) -> str:
        """A Python Pass is a UCLID5 empty statement."""
        return ""

    def visit_FunctionDef(self, node: FunctionDef) -> str:
        """A Python Function can be a few things in UCLID5:
        - state is where we declare variables
        - function_<name> is a define
        - procedure_<name> is a procedure
        - next is the transition relation
        - init is the initialization steps
        - specification holds all the invariants
        - proof is the control block
        """
        match node.name:
            case "state":
                return self.visit_state(node)
            case "next":
                return self.visit_next(node)
            case "init":
                return self.visit_init(node)
            case "specification":
                return self.visit_specification(node)
            case "proof":
                return self.visit_proof(node)
            case _ if node.name.startswith("function_"):
                return self.visit_define(node)
            case _ if node.name.startswith("procedure_"):
                return self.visit_procedure(node)
            case _:
                log(
                    f'`visit_FunctionDef` will return "" on {dump(node)}.',
                    Kind.WARNING,
                )
                return ""

    def visit_state(self, node: FunctionDef) -> str:
        """
        Python __init__ is where variables are declared.
        """
        body = node.body
        return "\n".join(map(self.visit_decls, body)) + "\n"

    def visit_decls(self, node) -> str:
        """A Python declaration is a UCLID5 variable declaration."""
        match node:
            case ast.Assign(targets, value, _):
                target = self.visit(targets[0])
                value = self.visit(value)
                value = infer_type(value)
                return f"var {target} : {value};"
            case _:
                log(
                    f'`visit_decls` will return "" on {dump(node)}.',
                    Kind.WARNING,
                )
                return ""

    def visit_next(self, node: FunctionDef) -> str:
        """
        next is the UCLID5 transition relation.
        """
        self.should_prime = True
        body = "\n".join(map(self.visit, node.body))
        self.should_prime = False
        if body:
            body = "\n" + body + "\n"
        return f"next {{{body}}}"

    def visit_init(self, node: FunctionDef) -> str:
        """
        init is the UCLID5 initialization block.
        """
        body = "\n".join(map(self.visit, node.body))
        if body:
            body = "\n" + body + "\n"
        return f"init {{{body}}}"

    def visit_proof(self, node: FunctionDef) -> str:
        """
        proof is the UCLID5 control block.
        """
        body = "\n".join(map(self.visit, node.body))
        if body:
            body = "\n" + body + "\n"
        return f"control {{{body}}}"

    def visit_specification(self, node: FunctionDef) -> str:
        """A Python specification is a function that returns a boolean."""
        body = node.body
        match body:
            case [ast.Return(value)]:
                value = self.visit(value)
                return f"invariant spec: {value};"
            case [v1, ast.Return(v2)] if self.visit(v1).startswith("//"):
                comment = self.visit(v1)
                value = self.visit(v2)
                return f"{comment}\ninvariant spec: {value};"
            case _:
                log(
                    f'`visit_specification` will return "" on {dump(node)}',
                    Kind.WARNING,
                )
                return ""

    def visit_define(self, node: FunctionDef) -> str:
        """A Python function is a UCLID5 define."""
        body = node.body
        return "\n".join(map(self.visit, body)) + "\n"

    def visit_procedure(self, node: FunctionDef) -> str:
        """A Python procedure is a UCLID5 procedure."""
        body = node.body
        return "\n".join(map(self.visit, body)) + "\n"

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
        func = self.visit(node.func)
        match func:
            case _ if func in support_dict:
                args = ", ".join(map(lambda arg: f'"{self.visit(arg)}"', node.args))
                return eval(f"{func}({args})")
            case _:
                log(
                    f'`visit_Call` will return "" on {dump(node)}.',
                    Kind.WARNING,
                )
                return ""

    def visit_Constant(self, node: Constant) -> str:
        """A Python constant is a UCLID5 literal"""
        if isinstance(node.value, str):
            log(
                f"`visit_Constant` will write a comment on {dump(node)}.",
                Kind.WARNING,
            )
            comment = "//"
            lines = node.value.split("\n")
            return "\n".join(map(lambda line: f"{comment} {line.strip()}", lines))
        return str(node.value)

    def visit_BinOp(self, node: BinOp) -> str:
        """A Python binary operation is a UCLID5 binary operation"""
        left = self.visit(node.left)
        right = self.visit(node.right)
        op = node.op
        if op.__class__.__name__ in operator_dict:
            op = operator_dict[op.__class__.__name__]
        else:
            log(
                f'`visit_BinOp` will return "" on {dump(node)}.',
                Kind.WARNING,
            )
            return ""
        return f"{left} {op} {right}"

    def visit_BoolOp(self, node: BoolOp) -> str:
        """A Python boolean operation is a UCLID5 boolean operation"""
        values = node.values
        op = node.op
        if op.__class__.__name__ in operator_dict:
            op = operator_dict[op.__class__.__name__]
        else:
            log(
                f'`visit_BoolOp` will return "" on {dump(node)}.',
                Kind.WARNING,
            )
            return ""
        return f" {op} ".join(map(self.visit, values))

    def visit_UnaryOp(self, node: UnaryOp) -> str:
        """A Python unary operation is a UCLID5 unary operation"""
        operand = self.visit(node.operand)
        op = node.op
        if op.__class__.__name__ in operator_dict:
            op = operator_dict[op.__class__.__name__]
        else:
            log(
                f'`visit_UnaryOp` will return "" on {dump(node)}.',
                Kind.WARNING,
            )
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
            log(
                f'`visit_AugAssing` will return "" on {dump(node)}.',
                Kind.WARNING,
            )
            return ""
        return f"{target_lhs} = {target} {op} {value};"

    def visit_With(self, node: With):
        """With statements are ignored."""
        log(
            f"`visit_With` will skip to the body of {dump(node)}.",
            Kind.WARNING,
        )
        body = "\n".join(map(self.visit, node.body))
        return body


def print_uclid5(node) -> str:
    """Print a UCLID5 expression."""
    return UclidPrinter().visit(node)
