import ast
import inspect
from _ast import Attribute, Call, FunctionDef, Pass
from typing import Any

from .types import integer_sort  # noqa: F401

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

    def visit_Module(self, node) -> str:
        """
        A Python Module is a UCLID5 file.
        """
        return "\n".join(map(self.visit, node.body))

    def visit_ClassDef(self, node) -> str:
        """
        A Python Class is a UCLID5 module.
        """
        body = "\n".join(map(self.visit, node.body))
        if body:
            body = "\n" + body + "\n"
        return f"module {node.name} {{{body}}}"

    def visit_Pass(self, _: Pass) -> str:
        """
        A Python Pass is a UCLID5 empty statement.
        """
        return ""

    def visit_FunctionDef(self, node: FunctionDef) -> str:
        """
        A Python Function can be a few things in UCLID5:
        - __init__ is where we declare variables
        - function_<name> is a define
        - procedure_<name> is a procedure
        - next is the transition relation
        - init is the initialization steps
        - invariant_<name> is an invariant
        - control is the control block
        """
        match node.name:
            case "__init__":
                return self.visit_state(node)
            case "next":
                return self.visit_next(node)
            case "init":
                return self.visit_init(node)
            case "control":
                return self.visit_control(node)
            case _ if node.name.startswith("invariant_"):
                return self.visit_invariant(node)
            case _ if node.name.startswith("function_"):
                return self.visit_define(node)
            case _ if node.name.startswith("procedure_"):
                return self.visit_procedure(node)
            case _:
                raise NotImplementedError(f"Function {node.name} not implemented")

    def visit_state(self, node: FunctionDef) -> str:
        """
        Python __init__ is where variables are declared.
        """
        body = node.body
        return "\n".join(map(self.visit_decls, body)) + "\n"

    def visit_decls(self, node: Any) -> str:
        """
        A Python declaration is a UCLID5 variable declaration.
        """
        match node:
            case ast.Assign(targets, value, _):
                target = self.visit(targets[0])
                value = self.visit(value)
                return f"var {target} : {value};"
            case _:
                raise NotImplementedError(f"Declaration {node} not implemented")

    def visit_next(self, node: FunctionDef) -> str:
        """
        A Python next is a UCLID5 transition relation.
        """
        body = node.body
        return "\n".join(map(self.visit, body)) + "\n"

    def visit_init(self, node: FunctionDef) -> str:
        """
        A Python init is a UCLID5 initialization block.
        """
        body = node.body
        return "\n".join(map(self.visit, body)) + "\n"

    def visit_control(self, node: FunctionDef) -> str:
        """
        A Python control is a UCLID5 control block.
        """
        body = node.body
        return "\n".join(map(self.visit, body)) + "\n"

    def visit_invariant(self, node: FunctionDef) -> str:
        """
        A Python invariant is a UCLID5 invariant.
        """
        body = node.body
        return "\n".join(map(self.visit, body)) + "\n"

    def visit_define(self, node: FunctionDef) -> str:
        """
        A Python function is a UCLID5 define.
        """
        body = node.body
        return "\n".join(map(self.visit, body)) + "\n"

    def visit_procedure(self, node: FunctionDef) -> str:
        """
        A Python procedure is a UCLID5 procedure.
        """
        body = node.body
        return "\n".join(map(self.visit, body)) + "\n"

    def visit_Assign(self, node) -> str:
        """
        A Python assignment is a UCLID5 assignment.
        """
        target = self.visit(node.targets[0])
        value = self.visit(node.value)
        return f"{target} = {value};"

    def visit_Attribute(self, node: Attribute) -> str:
        """
        A Python Attribute is a UCLID5 field access
        or, if the attribute is self, then it is ignored.
        """
        value = self.visit(node.value)
        attr = node.attr
        if value == "self":
            return attr
        return f"{value}.{attr}"

    def visit_Name(self, node) -> str:
        """
        A Python Name is a UCLID5 name
        """
        return node.id

    def visit_Call(self, node: Call) -> str:
        """
        A Python Call can be a few things in UCLID5:
        - a function call
        - a procedure call
        - a type constructor
        - or just a Python call that we want to execute
        """
        func = self.visit(node.func)
        args = ", ".join(map(self.visit, node.args))
        match func:
            case _ if func.startswith("function_"):
                offset = len("function_")
                return f"{func[offset:]}({args})"
            case _ if func.startswith("procedure_"):
                offset = len("procedure_")
                return f"call {func[offset:]}({args})"
            case _:
                return eval(f"{func}({args})")


class Module:
    def __str__(self) -> str:
        tree = ast.parse(inspect.getsource(self.__class__))
        return UclidPrinter().visit(tree)
