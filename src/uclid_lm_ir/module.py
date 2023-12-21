import ast
import inspect

def induction(k=1):
    return f"induction({k});"


def print_results():
    return "print_results();"


def check():
    return "check();"


def declare_var(name: str, type: str):
    return f"var {name}: {type};"


def int_type():
    return "integer"


def prime(name: str):
    return f"{name}'"


op_names = {
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
    "Pow": "**",
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
    "USub": "-"
}


class UclidPrinter(ast.NodeVisitor):
    def __init__(self) -> None:
        super().__init__()
        self.should_prime = False

    def visit(self, node) -> str:
        match node:
            case ast.Module(body, _):
                return "\n".join(map(self.visit, body))
            case ast.ClassDef(name, _, _, body, _):
                body = "\n".join(map(self.visit, body))
                return f"module {name} {{\n{body}\n}}"
            case ast.FunctionDef("state", _, body, _, _):
                return "\n".join(map(self.visit, body)) + "\n"
            case ast.FunctionDef("base", _, body, _, _):
                body = "\n".join(map(self.visit, body))
                return f"init {{\n{body}\n}}\n"
            case ast.FunctionDef("step", _, body, _, _):
                self.should_prime = True
                body = "\n".join(map(self.visit, body))
                self.should_prime = False
                return f"next {{\n{body}\n}}\n"
            case ast.FunctionDef("control", _, body, _, _):
                body = "\n".join(map(self.visit, body))
                return f"control {{\n{body}\n}}"
            case ast.FunctionDef(name, _, body, _, _) if name.startswith("invariant_"):
                # get the name after invariant_
                name = name[len("invariant_"):]
                assert len(body) == 1
                body = self.visit(body[0])
                return f"invariant {name}: {body};\n"
            case ast.Assign(targets, value, _) if isinstance(value, ast.Call) and value.func.id == "declare_var":
                return self.visit(value)
            case ast.Assign(targets, value, _):
                targets = ", ".join(map(lambda x: self.visit(
                    x) + ("'" if self.should_prime else ""), targets))
                return f"{targets} = {self.visit(value)};"
            case ast.Attribute(value, attr, _) if value.id == "self":
                return attr
            case ast.Call(func, args, _):
                func = self.visit(func)
                args = ", ".join(map(lambda x: f"\"{self.visit(x)}\"", args))
                return eval(f"{func}({args})")
            case ast.Name(id, _):
                return id
            case ast.Constant(value, _):
                return str(value)
            case ast.BinOp(left, op, right):
                left = self.visit(left)
                right = self.visit(right)
                return f"{left} {op_names[op.__class__.__name__]} {right}"
            case ast.UnaryOp(op, operand):
                operand = self.visit(operand)
                return f"{op_names[op.__class__.__name__]}{operand}"
            case ast.Compare(left, ops, comparators):
                left = self.visit(left)
                ops = " ".join(
                    map(lambda x: op_names[x.__class__.__name__], ops))
                comparators = " ".join(map(self.visit, comparators))
                return f"{left} {ops} {comparators}"
            case ast.Expr(value):
                return self.visit(value)
            case _:
                raise NotImplementedError(
                    f"Node type {type(node)} not implemented:\n{ast.dump(node, indent=2)}")


class Module:
    def __str__(self) -> str:
        tree = ast.parse(inspect.getsource(self.__class__))
        return UclidPrinter().visit(tree)
