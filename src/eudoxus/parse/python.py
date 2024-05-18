from typing import List, Tuple

import tree_sitter_python as ts
from tree_sitter import Language as TSLanguage
from tree_sitter import Node as TSNode
from tree_sitter import Parser as TSParser

import eudoxus.ast.expression as e
import eudoxus.ast.proof as p
import eudoxus.ast.statement as s
import eudoxus.ast.type as t
from eudoxus.ast.module import Module
from eudoxus.ast.node import HoleId, Identifier, Position
from eudoxus.utils import foldl

RESERVED_STATEMENTS = ["assume", "assert", "havoc"]

PY_LANGUAGE = TSLanguage(ts.language(), "python")


def search(query: str, node: TSNode) -> List[TSNode]:
    query = query + " @target"
    matches = PY_LANGUAGE.query(query).matches(node)
    return [m[1]["target"] for m in matches]


class Parser:
    def __init__(self, src, debug=False):
        self.debug = debug

        parser = TSParser()
        parser.set_language(PY_LANGUAGE)

        def read_callable_byte_offset(byte_offset, _):
            return src[byte_offset : byte_offset + 1]

        self.text = lambda node: src[node.start_byte : node.end_byte].decode("utf-8")

        self.tree = parser.parse(read_callable_byte_offset)

        self.enum_count = 0
        self.position_count = 1

    def fpos(self) -> Position:
        self.position_count += 1
        return Position(self.position_count)

    def search(self, func, node: TSNode, strict=True) -> List[TSNode]:
        """
        Returns a list of nodes that match the query in the docstring of the function.
        This is a trick to be able to use docstrings as queries (preconditions)

        params:
            func: a function whose docstring contains the query
            node: the node to search in
            strict: if True, only return nodes that are direct children of the node
        """
        if node is None:
            return []
        to_search = func.__doc__
        while "{" in to_search:
            to_search = f'f"""{to_search}"""'
            to_search = eval(to_search)
        results = search(to_search, node)
        if strict:
            return [r for r in results if r.parent == node]
        return results

    def parse(self):
        modules = self.search(self.parse_module, self.tree.root_node, strict=False)
        modules = [self.parse_module(module) for module in modules]
        return modules

    def parse_flat_identifier(self, node: TSNode) -> Identifier:
        """(identifier)"""
        return Identifier(self.fpos(), self.text(node))

    def parse_self_identifier(self, node: TSNode) -> Identifier:
        """
        (attribute
            object: (identifier)
            attribute: (identifier))
        """
        object = self.text(node.child_by_field_name("object"))
        attribute = self.text(node.child_by_field_name("attribute"))
        match object:
            case "self":
                return Identifier(self.fpos(), attribute)
            case "random" if attribute.lower() in ["random", "choice"]:
                return Identifier(self.fpos(), attribute)
            case _ if self.debug:
                raise ValueError(f"Unsupported object: {node.sexp()}")
            case _:
                return HoleId(self.fpos())

    def parse_identifier(self, node: TSNode) -> Identifier:
        """
        [
            {self.parse_flat_identifier.__doc__}
            {self.parse_self_identifier.__doc__}
        ]
        """
        if node is None:
            return HoleId(self.fpos())
        match node.type:
            case "identifier":
                return self.parse_flat_identifier(node)
            case "attribute":
                return self.parse_self_identifier(node)
            case _ if self.debug:
                raise ValueError(f"Unsupported object: {node.sexp()}")
            case _:
                return HoleId(self.fpos())

    def type_helper(self, id: Identifier, args: TSNode) -> t.Type:
        name = id.name
        if "bool" in name.lower():
            return t.BooleanType(self.fpos())
        elif "int" in name.lower():
            return t.IntegerType(self.fpos())
        elif "real" in name.lower():
            return t.RealType(self.fpos())
        elif "bv" in name.lower() or "bitvector" in name.lower():
            size = self.search(self.parse_integer, args)[0]
            size = self.parse_integer(size).value
            return t.BitVectorType(self.fpos(), size)
        elif "array" in name.lower():
            args_list = self.search(self.parse_type_expr, args)
            if len(args_list) == 0:
                args_list = self.search(self.parse_keyword_type_argument, args)
                args_list = [
                    self.parse_keyword_type_argument(arg)[1] for arg in args_list
                ]
                index_t = args_list[0]
                elem_t = args_list[1]
            elif len(args_list) == 2:
                index_t = self.parse_type_expr(args_list[0])
                elem_t = self.parse_type_expr(args_list[1])
            elif self.debug:
                raise ValueError(f"Unsupported object: {self.text(args)}")
            else:
                return t.HoleType(self.fpos())
            return t.ArrayType(self.fpos(), index_t, elem_t)
        elif "enum" in name.lower():
            if (
                args is not None
                and args.child_count >= 4
                and args.child(1).type == "string"
                and args.child(3).type == "list"
            ):
                # e.g., Enum('t', ['B', 'C'])
                args = args.child(3)

            args_list = self.search(self.parse_string, args, strict=False)
            args_list = [self.parse_string(arg) for arg in args_list]
            if len(args_list) == 1 and " " in args_list[0]:
                args_list = args_list[0].split(" ")
            args_list = [Identifier(self.fpos(), arg) for arg in args_list]

            if len(args_list) == 0:
                args_list = self.search(self.parse_integer, args, strict=False)
                args_list = [self.parse_integer(arg) for arg in args_list]
                k = args_list[0] if len(args_list) > 0 else 0
                args_list = []
                for _ in range(k.value):
                    args_list.append(
                        Identifier(self.fpos(), "anon_enum_" + str(self.enum_count))
                    )
                    self.enum_count += 1
            return t.EnumeratedType(self.fpos(), args_list)
        elif "record" in name.lower():
            fields = self.search(self.parse_string_type_pair, args, strict=False)
            fields = [self.parse_string_type_pair(field) for field in fields]
            return t.RecordType(self.fpos(), fields)
        else:
            return t.SynonymType(self.fpos(), id)

    def parse_app_type(self, node: TSNode) -> t.Type:
        """
        (call
            function: {self.parse_identifier.__doc__}
            arguments: (argument_list))
        """
        function = self.parse_identifier(node.child_by_field_name("function"))
        arguments = node.child_by_field_name("arguments")
        return self.type_helper(function, arguments)

    def parse_type_expr(self, node: TSNode) -> t.Type:
        """
        [
            {self.parse_flat_identifier.__doc__}
            {self.parse_self_identifier.__doc__}
            {self.parse_app_type.__doc__}
        ]
        """
        match node.type:
            case "identifier" | "attribute":
                return self.type_helper(self.parse_identifier(node), None)
            case "call":
                return self.parse_app_type(node)
            case _ if self.debug:
                raise ValueError(f"Unsupported object: {node.sexp()}")
            case _:
                return t.HoleType(self.fpos())

    def parse_type_declaration(self, node: TSNode) -> s.TypeDecl:
        """
        (assignment
            left: {self.parse_identifier.__doc__}
            right: {self.parse_type_expr.__doc__})
        """
        id = self.parse_identifier(node.child_by_field_name("left"))
        rhs = self.parse_type_expr(node.child_by_field_name("right"))
        if isinstance(rhs, t.EnumeratedType):
            fst = rhs.values[0]
            if fst.name == id.name:
                # e.g., self.t = Enum('t', 'A', 'B', 'C')
                rhs = t.EnumeratedType(self.fpos(), rhs.values[1:])

        return s.TypeDecl(self.fpos(), id, rhs)

    def parse_name_type_pair(self, node: TSNode) -> Tuple[Identifier, t.Type]:
        """
        (tuple
            ({self.parse_identifier.__doc__})
            ({self.parse_type_expr.__doc__})
        )
        """
        id = self.parse_identifier(node.child(1))
        ty = self.parse_type_expr(node.child(3))
        return (id, ty)

    def parse_string_type_pair(self, node: TSNode) -> Tuple[Identifier, t.Type]:
        """
        (tuple
            (string)
            ({self.parse_type_expr.__doc__})
        )
        """
        id = self.parse_string(node.child(1))
        id = Identifier(self.fpos(), id)
        ty = self.parse_type_expr(node.child(3))
        return (id, ty)

    def expr_helper(
        self,
        pos: Position,
        f: str,
        args: List[e.Expression],
        kwargs: List[Tuple[Identifier, e.Expression]],
    ) -> e.Expression:
        match f.lower():
            case bv if "bv" in bv or "bitvec" in bv:
                match args, kwargs:
                    case [e.IntegerValue(_, value), e.IntegerValue(_, size)], []:
                        return e.BitVectorValue(pos, value, size)
                    case [e.IntegerValue(_, size)], [
                        (Identifier(_, "value"), e.IntegerValue(_, value))
                    ]:
                        return e.BitVectorValue(pos, value, size)
                    case [e.IntegerValue(_, value)], [
                        (Identifier(_, "width"), e.IntegerValue(_, size))
                    ]:
                        return e.BitVectorValue(pos, value, size)
                    case [], [
                        (Identifier(_, "width"), e.IntegerValue(_, size)),
                        (Identifier(_, "value"), e.IntegerValue(_, value)),
                    ]:
                        return e.BitVectorValue(pos, value, size)
                    case _ if self.debug:
                        raise ValueError(f"Unsupported args: {args}")
                    case _:
                        return e.HoleExpr(pos)
            case "not" | "neg" if len(args) == 1:
                return e.Not(pos, *args)
            case "neg" | "negative" | "negate" if len(args) == 1:
                return e.Negate(pos, *args)
            case "and" | "conjunct" | "conjunction" if 1 <= len(args) <= 2:
                if len(args) == 1:
                    return args[0]
                return e.And(pos, *args)
            case "or" | "disjunct" | "disjunction" if 1 <= len(args) <= 2:
                if len(args) == 1:
                    return args[0]
                return e.Or(pos, *args)
            case "xor" | "exclusive_or" if 1 <= len(args) <= 2:
                if len(args) == 1:
                    return args[0]
                return e.Xor(pos, *args)
            case "implies" | "impl" | "if_" if 1 <= len(args) <= 2:
                if len(args) == 1:
                    return args[0]
                return e.Implies(pos, *args)
            case "iff" | "equiv" | "eq" | "equal" if 1 <= len(args) <= 2:
                if len(args) == 1:
                    return args[0]
                return e.Equal(pos, *args)
            case "add" | "plus" | "sum" | "addition" if 1 <= len(args) <= 2:
                if len(args) == 1:
                    return args[0]
                return e.Add(pos, *args)
            case "sub" | "subtract" | "minus" if 1 <= len(args) <= 2:
                if len(args) == 1:
                    return args[0]
                return e.Subtract(pos, *args)
            case "mul" | "multiply" | "times" | "mult" if 1 <= len(args) <= 2:
                if len(args) == 1:
                    return args[0]
                return e.Multiply(pos, *args)
            case "div" | "divide" | "quotient" if 1 <= len(args) <= 2:
                if len(args) == 1:
                    return args[0]
                return e.Divide(pos, *args)
            case "mod" | "modulo" | "remainder" | "modulus" if 1 <= len(args) <= 2:
                if len(args) == 1:
                    return args[0]
                return e.Modulo(pos, *args)
            case "neq" | "notequal" if 1 <= len(args) <= 2:
                if len(args) == 1:
                    return args[0]
                return e.NotEqual(pos, *args)
            case "lt" | "lessthan" if 1 <= len(args) <= 2:
                if len(args) == 1:
                    return args[0]
                return e.LessThan(pos, *args)
            case "le" | "lte" | "lessthanorequal" if 1 <= len(args) <= 2:
                if len(args) == 1:
                    return args[0]
                return e.LessThanOrEqual(pos, *args)
            case "gt" | "greaterthan" if 1 <= len(args) <= 2:
                if len(args) == 1:
                    return args[0]
                return e.GreaterThan(pos, *args)
            case "ge" | "gte" | "greaterthanorequal" if 1 <= len(args) <= 2:
                if len(args) == 1:
                    return args[0]
                return e.GreaterThanOrEqual(pos, *args)
            case "select" | "sel" if 1 <= len(args) <= 2:
                if len(args) == 1:
                    return args[0]
                return e.RecordSelect(pos, *args)
            case "ite" | "ifthenelse" | "ifelse" | "if" | "if_" if len(args) == 3:
                return e.Ite(pos, *args)
            case "random" | "rand" | "choice" | "nondet":
                return e.Nondet(pos)
            case _ if self.debug:
                raise ValueError(f"Unsupported function: {f}({args})")
            case _:
                return e.HoleExpr(pos)

    def parse_app_expr(self, node: TSNode) -> e.Expression:
        """
        (call
            function: {self.parse_identifier.__doc__}
            arguments: (argument_list))
        """

        def parse_args() -> List[e.Expression]:
            arguments = self.search(
                self.parse_expr, node.child_by_field_name("arguments")
            )
            arguments = [self.parse_expr(arg) for arg in arguments]
            kwargs = self.search(
                self.parse_keyword_argument, node.child_by_field_name("arguments")
            )
            kwargs = [self.parse_keyword_argument(kw) for kw in kwargs]
            return arguments, kwargs

        fnode = node.child_by_field_name("function")
        function = self.parse_identifier(fnode)
        match function.name.lower():
            case "forall" | "exists":
                quant = e.Forall if function.name.lower() == "forall" else e.Exists

                arguments = node.child_by_field_name("arguments")

                # first look for identifier-type pairs
                bindings = self.search(
                    self.parse_name_type_pair, arguments, strict=False
                )
                bindings = [self.parse_name_type_pair(binding) for binding in bindings]
                if len(bindings) > 0:
                    # then we had Forall([(x1, t1), ..., (xn, tn)], body)
                    body = self.search(self.parse_expr, arguments)
                    body = self.parse_expr(body[0])
                    return foldl(
                        lambda x, y: quant(self.fpos(), *x, y),
                        quant(self.fpos(), *bindings[0], body),
                        bindings[1:],
                    )
                elif len(arguments.children) == 7:
                    # then we had Forall(x1, t1, body)
                    x = self.parse_identifier(arguments.children[1])
                    ty = self.parse_type_expr(arguments.children[3])
                    body = self.parse_expr(arguments.children[5])
                    return quant(self.fpos(), x, ty, body)
                elif len(arguments.children) == 5:
                    # then we had Forall(x1, body)
                    x = self.parse_identifier(arguments.children[1])
                    body = self.parse_expr(arguments.children[3])
                    return quant(self.fpos(), x, t.HoleType(self.fpos()), body)
                else:
                    if self.debug:
                        raise ValueError(
                            f"Unsupported object: {len(arguments.children)}"
                        )
                    return e.HoleExpr(self.fpos())
            case _:
                arguments, kwargs = parse_args()
                return self.expr_helper(self.fpos(), function.name, arguments, kwargs)

    def parse_app_of_app_expr(self, node: TSNode) -> e.Expression:
        """
        (call
            function: (call
                function: {self.parse_identifier.__doc__}
                arguments: (argument_list))
            arguments: (argument_list))
        """
        call = node.child_by_field_name("function")
        inner_args = call.child_by_field_name("arguments")
        outer_args = node.child_by_field_name("arguments")

        function = self.parse_identifier(call.child_by_field_name("function"))
        outer_args = self.search(self.parse_expr, outer_args)
        outer_args = [self.parse_expr(arg) for arg in outer_args]
        inner_args = self.search(self.parse_expr, inner_args)
        inner_args = [self.parse_expr(arg) for arg in inner_args]
        arguments = outer_args + inner_args
        return self.expr_helper(self.fpos(), function.name, arguments, [])

    def parse_subscript_expr(self, node: TSNode) -> e.ArraySelect:
        """
        (subscript
            value: (_)
            subscript: (_))
        """
        array = self.parse_expr(node.child_by_field_name("value"))
        index = self.parse_expr(node.child_by_field_name("subscript"))
        return e.ArraySelect(self.fpos(), array, index)

    def parse_error(self, node: TSNode) -> str:
        """(ERROR)"""
        return self.text(node)

    def parse_select_expr(self, node: TSNode) -> e.RecordSelect:
        """
        (attribute
            object: (_)
            attribute: (_))
        """
        record = self.parse_expr(node.child_by_field_name("object"))
        selector = self.parse_identifier(node.child_by_field_name("attribute"))
        return e.RecordSelect(self.fpos(), record, selector)

    def parse_conditional_expression(self, node: TSNode) -> e.Expression:
        """
        (conditional_expression)
        """
        consequence = self.parse_expr(node.child(0))
        condition = self.parse_expr(node.child(2))
        alternative = self.parse_expr(node.child(4))
        return e.Ite(self.fpos(), condition, consequence, alternative)

    def parse_boolean_expression(self, node: TSNode) -> e.Expression:
        """
        (boolean_operator
            left: (_)
            right: (_))
        """
        left = self.parse_expr(node.child_by_field_name("left"))
        right = self.parse_expr(node.child_by_field_name("right"))
        match self.text(node.child_by_field_name("operator")):
            case "and":
                return e.And(self.fpos(), left, right)
            case "or":
                return e.Or(self.fpos(), left, right)
            case "not":
                return e.Not(self.fpos(), left)
            case _ if self.debug:
                raise ValueError(f"Unsupported object: {node.sexp()}")
            case _:
                return e.HoleExpr(self.fpos())

    def parse_comparison_expression(self, node: TSNode) -> e.Expression:
        """
        (comparison_operator)
        """

        def helper(op, left, right):
            match op:
                case "==":
                    return e.Equal(self.fpos(), left, right)
                case "!=":
                    return e.NotEqual(self.fpos(), left, right)
                case "<":
                    return e.LessThan(self.fpos(), left, right)
                case ">":
                    return e.GreaterThan(self.fpos(), left, right)
                case "<=":
                    return e.LessThanOrEqual(self.fpos(), left, right)
                case ">=":
                    return e.GreaterThanOrEqual(self.fpos(), left, right)
                case _ if self.debug:
                    raise ValueError(f"Unsupported object: {node.sexp()}")
                case _:
                    return e.HoleExpr(self.fpos())

        args = self.search(self.parse_expr, node)
        args = [self.parse_expr(arg) for arg in args]

        ops = [self.text(node.child(i)) for i in range(1, node.child_count, 2)]

        base = e.HoleExpr(self.fpos())
        for i, arg in enumerate(args):
            if i == 0:
                continue
            elif i == 1:
                base = helper(ops[i - 1], args[i - 1], arg)
            else:
                term = helper(ops[i - 1], args[i - 1], arg)
                base = e.And(self.fpos(), base, term)

        return base

    def parse_unary_expression(self, node: TSNode) -> e.Expression:
        """
        (unary_operator)
        """
        arg = self.parse_expr(node.child_by_field_name("argument"))
        match self.text(node.child_by_field_name("operator")):
            case "-":
                return e.Negate(self.fpos(), arg)
            case _ if self.debug:
                raise ValueError(f"Unsupported object: {node.sexp()}")
            case _:
                return e.HoleExpr(self.fpos())

    def parse_not_expression(self, node: TSNode) -> e.Expression:
        """
        (not_operator)
        """
        arg = self.parse_expr(node.child_by_field_name("argument"))
        return e.Not(self.fpos(), arg)

    def parse_binary_expression(self, node: TSNode) -> e.Expression:
        """
        (binary_operator
            left: (_)
            right: (_))
        """
        left = self.parse_expr(node.child_by_field_name("left"))
        right = self.parse_expr(node.child_by_field_name("right"))
        match self.text(node.child_by_field_name("operator")):
            case "+":
                return e.Add(self.fpos(), left, right)
            case "-":
                return e.Subtract(self.fpos(), left, right)
            case "*":
                return e.Multiply(self.fpos(), left, right)
            case "/":
                return e.Divide(self.fpos(), left, right)
            case "%":
                return e.Modulo(self.fpos(), left, right)
            case _ if self.debug:
                raise ValueError(f"Unsupported object: {node.sexp()}")
            case _:
                return e.HoleExpr(self.fpos())

    def parse_integer(self, node: TSNode) -> e.Value:
        """(integer)"""
        return e.IntegerValue(self.fpos(), int(self.text(node)))

    def parse_float(self, node: TSNode) -> e.Value:
        """(float)"""
        return e.RealValue(self.fpos(), float(self.text(node)))

    def parse_boolean(self, node: TSNode) -> e.Value:
        """
        [
            (true)
            (false)
        ]
        """
        return e.BooleanValue(self.fpos(), self.text(node) == "True")

    def parse_string(self, node: TSNode) -> str:
        """(string)"""
        return self.text(node)[1:-1]

    def parse_variant(self, node: TSNode) -> e.Value:
        """(string)"""
        return e.EnumValue(self.fpos(), self.parse_string(node))

    def parse_expr(self, node: TSNode) -> e.Expression:
        """
        [
            {self.parse_flat_identifier.__doc__}
            {self.parse_self_identifier.__doc__}
            {self.parse_variant.__doc__}
            {self.parse_select_expr.__doc__}
            {self.parse_subscript_expr.__doc__}
            {self.parse_app_expr.__doc__}
            {self.parse_app_of_app_expr.__doc__}
            {self.parse_not_expression.__doc__}
            {self.parse_unary_expression.__doc__}
            {self.parse_binary_expression.__doc__}
            {self.parse_comparison_expression.__doc__}
            {self.parse_boolean_expression.__doc__}
            {self.parse_conditional_expression.__doc__}
            (true)
            (false)
            {self.parse_integer.__doc__}
            {self.parse_float.__doc__}
            (parenthesized_expression)
        ]
        """
        errors = self.search(self.parse_error, node)
        if len(errors) > 0 and self.debug:
            raise ValueError(f"Errors: {[self.parse_error(e) for e in errors]}")
        elif len(errors) > 0:
            return e.HoleExpr(self.fpos())
        match node.type:
            case "identifier":
                id = self.parse_flat_identifier(node)
                return e.FunctionApplication(self.fpos(), id, [])
            case "attribute" if self.text(node.child_by_field_name("object")) == "self":
                id = self.parse_self_identifier(node)
                return e.FunctionApplication(self.fpos(), id, [])
            case "attribute":
                return self.parse_select_expr(node)
            case "subscript":
                return self.parse_subscript_expr(node)
            case "call" if node.child_by_field_name("function").type == "call":
                return self.parse_app_of_app_expr(node)
            case "call":
                return self.parse_app_expr(node)
            case "unary_operator":
                return self.parse_unary_expression(node)
            case "not_operator":
                return self.parse_not_expression(node)
            case "binary_operator":
                return self.parse_binary_expression(node)
            case "comparison_operator":
                return self.parse_comparison_expression(node)
            case "boolean_operator":
                return self.parse_boolean_expression(node)
            case "conditional_expression":
                return self.parse_conditional_expression(node)
            case "integer":
                return self.parse_integer(node)
            case "true" | "false":
                return self.parse_boolean(node)
            case "string":
                return self.parse_variant(node)
            case "float":
                return self.parse_float(node)
            case "parenthesized_expression":
                return self.parse_expr(node.child(1))
            case _ if self.debug:
                raise ValueError(
                    f"Unsupported object: {node.sexp()} of type {node.type}"
                )
            case _:
                return e.HoleExpr(self.fpos())

    def parse_var_declaration(self, node: TSNode, kind: str) -> s.VariableDecl:
        """
        (assignment
            left: {self.parse_identifier.__doc__}
            right: {self.parse_type_expr.__doc__})
        """
        id = self.parse_identifier(node.child_by_field_name("left"))
        rhs = self.parse_type_expr(node.child_by_field_name("right"))
        match kind:
            case "locals":
                return s.LocalDecl(self.fpos(), id, rhs)
            case "inputs":
                return s.InputDecl(self.fpos(), id, rhs)
            case "outputs":
                return s.OutputDecl(self.fpos(), id, rhs)
            case "sharedvars":
                return s.SharedDecl(self.fpos(), id, rhs)
            case _ if self.debug:
                raise ValueError(f"Unsupported object: {kind}")
            case _:
                return s.LocalDecl(self.fpos(), id, rhs)

    def parse_keyword_type_argument(self, node: TSNode) -> Tuple[Identifier, t.Type]:
        """
        (keyword_argument
            name: {self.parse_identifier.__doc__}
            value: {self.parse_type_expr.__doc__})
        """
        name = self.parse_identifier(node.child_by_field_name("name"))
        value = self.parse_type_expr(node.child_by_field_name("value"))
        return (name, value)

    def parse_keyword_argument(self, node: TSNode) -> Tuple[Identifier, e.Expression]:
        """
        (keyword_argument
            name: {self.parse_identifier.__doc__}
            value: {self.parse_expr.__doc__})
        """
        name = self.parse_identifier(node.child_by_field_name("name"))
        value = self.parse_expr(node.child_by_field_name("value"))
        return (name, value)

    def parse_instances_declaration(self, node: TSNode) -> s.InstanceDecl:
        """
        (assignment
            left: {self.parse_identifier.__doc__}
            right: (call
                function: {self.parse_identifier.__doc__}
                arguments: (argument_list)))
        """
        target = self.parse_identifier(node.child_by_field_name("left"))
        call = node.child_by_field_name("right")
        mod = self.parse_identifier(call.child_by_field_name("function"))
        args = call.child_by_field_name("arguments")
        args = self.search(self.parse_keyword_argument, args)
        args = [self.parse_keyword_argument(arg) for arg in args]
        return s.InstanceDecl(self.fpos(), target, mod, args)

    def parse_assignment(self, node: TSNode) -> s.Assignment:
        """
        (expression_statement
            (assignment
                left: {self.parse_expr.__doc__}
                right: {self.parse_expr.__doc__}))
        """
        node = node.child(0)
        rhs = self.parse_expr(node.child_by_field_name("right"))
        lhs = self.parse_expr(node.child_by_field_name("left"))
        match lhs:
            case e.ArraySelect(_, array, index):
                lhs = array
                rhs = e.ArrayStore(self.fpos(), array, index, rhs)
        return s.Assignment(self.fpos(), lhs, rhs)

    def parse_augmented_assignment(self, node: TSNode) -> s.Assignment:
        """
        (expression_statement
            (augmented_assignment
                left: {self.parse_expr.__doc__}
                right: {self.parse_expr.__doc__}))
        """
        node = node.child(0)
        rhs = self.parse_expr(node.child_by_field_name("right"))
        lhs = self.parse_expr(node.child_by_field_name("left"))
        match node.child(1).type:
            case "+=":
                rhs = e.Add(self.fpos(), lhs, rhs)
            case "-=":
                rhs = e.Subtract(self.fpos(), lhs, rhs)
            case "*=":
                rhs = e.Multiply(self.fpos(), lhs, rhs)
            case "/=":
                rhs = e.Divide(self.fpos(), lhs, rhs)
            case "%=":
                rhs = e.Modulo(self.fpos(), lhs, rhs)
            case _ if self.debug:
                raise ValueError(f"Unsupported object: {node.sexp()}")
            case _:
                return s.HoleStmt(self.fpos())
        return s.Assignment(self.fpos(), lhs, rhs)

    def parse_elif(self, node: TSNode) -> Tuple[e.Expression, s.Block]:
        """
        (elif_clause
            condition: (_)
            consequence: (_))
        """
        condition = self.parse_expr(node.child_by_field_name("condition"))
        consequence = self.search(
            self.parse_statement, node.child_by_field_name("consequence")
        )
        consequence = s.Block(
            self.fpos(), [self.parse_statement(stmt) for stmt in consequence]
        )
        return (condition, consequence)

    def parse_else(self, node: TSNode) -> s.Block:
        """
        (else_clause
            body: (_))
        """
        body = self.search(self.parse_statement, node.child_by_field_name("body"))
        body = s.Block(self.fpos(), [self.parse_statement(stmt) for stmt in body])
        return body

    def parse_if_statement(self, node: TSNode) -> s.If:
        """
        (if_statement)
        """
        condition = self.parse_expr(node.child_by_field_name("condition"))
        consequence = self.search(
            self.parse_statement, node.child_by_field_name("consequence")
        )
        consequence = s.Block(
            self.fpos(), [self.parse_statement(stmt) for stmt in consequence]
        )
        elifs = self.search(self.parse_elif, node)
        elifs = [self.parse_elif(elif_) for elif_ in elifs][::-1]
        else_ = self.search(self.parse_else, node)
        if len(else_) != 1:
            else_ = s.Block(self.fpos(), [])
        else:
            else_ = self.parse_else(else_[0])

        inner = foldl(
            lambda acc, x: s.Block(self.fpos(), [s.If(self.fpos(), x[0], x[1], acc)]),
            else_,
            elifs,
        )
        return s.If(self.fpos(), condition, consequence, inner)

    def parse_with_statement(self, node: TSNode) -> s.If:
        """
        (with_statement)
        """
        body = self.search(self.parse_statement, node.child_by_field_name("body"))
        body = s.Block(self.fpos(), [self.parse_statement(stmt) for stmt in body])
        return s.If(
            self.fpos(), e.HoleExpr(self.fpos()), body, s.Block(self.fpos(), [])
        )

    def parse_step_statement(self, node: TSNode) -> s.Next:
        """
        (expression_statement
            (call
                function: (attribute)
                arguments: (argument_list)))
        """
        attribute = node.child(0).child_by_field_name("function")
        id = self.parse_identifier(attribute.child_by_field_name("object"))
        next_call = self.parse_identifier(attribute.child_by_field_name("attribute"))
        next_call = next_call.name.lower()
        match next_call:
            case "next":
                return s.Next(self.fpos(), id)
            case _ if self.debug:
                raise ValueError(f"Unsupported object: {node.sexp()}")
            case _:
                return s.HoleStmt(self.fpos())

    def parse_havoc_statement(self, node: TSNode) -> s.Havoc:
        """
        (expression_statement
            (call
                function: {self.parse_identifier.__doc__}
                arguments: (argument_list)))
        """
        call = node.child(0)
        function = self.parse_identifier(call.child_by_field_name("function"))
        args = call.child_by_field_name("arguments")
        args = self.search(self.parse_identifier, args)
        args = [self.parse_identifier(arg) for arg in args]
        match function.name:
            case "havoc" if len(args) == 1:
                return s.Havoc(self.fpos(), args[0])
            case _ if self.debug:
                raise ValueError(f"Unsupported object: {node.sexp()}")
            case _:
                return s.HoleStmt(self.fpos())

    def parse_assume_statement(self, node: TSNode) -> s.Assume:
        """
        (expression_statement
            (call
                function: {self.parse_identifier.__doc__}
                arguments: (argument_list)))
        """
        call = node.child(0)
        function = self.parse_identifier(call.child_by_field_name("function"))
        args = call.child_by_field_name("arguments")
        args = self.search(self.parse_expr, args)
        args = [self.parse_expr(arg) for arg in args]
        match function.name:
            case "assume" if len(args) == 1:
                return s.Assume(self.fpos(), args[0])
            case _ if self.debug:
                raise ValueError(f"Unsupported object: {node.sexp()}")
            case _:
                return s.HoleStmt(self.fpos())

    def parse_assert_statement(self, node: TSNode) -> s.Assert:
        """
        (assert_statement)
        """
        condition = node.child(1)
        condition = self.parse_expr(condition)
        return s.Assert(self.fpos(), condition)

    def parse_statement(self, node: TSNode) -> s.Statement:
        """
        [
            {self.parse_assignment.__doc__}
            {self.parse_augmented_assignment.__doc__}
            {self.parse_if_statement.__doc__}
            {self.parse_with_statement.__doc__}
            {self.parse_assert_statement.__doc__}
            {self.parse_assume_statement.__doc__}
            {self.parse_havoc_statement.__doc__}
            {self.parse_step_statement.__doc__}
        ]
        """

        def get_func_name(node: TSNode) -> str:
            match node.type:
                case "expression_statement":
                    match node.child(0).type:
                        case "call":
                            return self.text(
                                node.child(0).child_by_field_name("function")
                            )
            return ""

        def is_reserved(reserved: str) -> bool:
            return reserved.lower() in RESERVED_STATEMENTS

        match node.type:
            case "if_statement":
                return self.parse_if_statement(node)
            case "with_statement":
                return self.parse_with_statement(node)
            case "assert_statement":
                return self.parse_assert_statement(node)
            case "expression_statement" if is_reserved(get_func_name(node)):
                reserved = get_func_name(node)
                match reserved:
                    case "assume":
                        return self.parse_assume_statement(node)
                    case "assert":
                        return self.parse_assert_statement(node)
                    case "havoc":
                        return self.parse_havoc_statement(node)
            case "expression_statement" if node.child(0).type == "augmented_assignment":
                return self.parse_augmented_assignment(node)
            case "expression_statement" if node.child(0).type == "call":
                return self.parse_step_statement(node)
            case "expression_statement":
                return self.parse_assignment(node)
            case _ if self.debug:
                raise ValueError(f"Unsupported object: {node.sexp()}")
            case _:
                return s.HoleStmt(self.fpos())

    def parse_type_block(self, node: TSNode) -> s.Block:
        """
        (function_definition
            name: (identifier)
            parameters: (parameters)
            body: (block))
        """
        name = self.text(node.child_by_field_name("name"))
        body = node.child_by_field_name("body")
        match name:
            case "types":
                decls = self.search(self.parse_type_declaration, body, strict=False)
                decls = s.Block(
                    self.fpos(), [self.parse_type_declaration(decl) for decl in decls]
                )
                return decls
            case _ if self.debug:
                raise ValueError(f"Unsupported object: {name}")
            case _:
                return s.HoleStmt(self.fpos())

    def parse_var_block(self, node: TSNode, kind: str) -> s.Block:
        """
        (function_definition
            name: (identifier)
            parameters: (parameters)
            body: (block))
        """
        name = self.text(node.child_by_field_name("name"))
        body = node.child_by_field_name("body")
        if name == kind:
            decls = self.search(self.parse_var_declaration, body, strict=False)
            decls = s.Block(
                self.fpos(), [self.parse_var_declaration(decl, kind) for decl in decls]
            )
            return decls
        elif self.debug:
            raise ValueError(f"Unsupported object: {name}")
        else:
            return s.HoleStmt(self.fpos())

    def parse_instances_block(self, node: TSNode) -> s.Block:
        """
        (function_definition
            name: (identifier)
            parameters: (parameters)
            body: (block))
        """
        name = self.text(node.child_by_field_name("name"))
        body = node.child_by_field_name("body")
        if name == "instances":
            decls = self.search(self.parse_instances_declaration, body, strict=False)
            decls = s.Block(
                self.fpos(), [self.parse_instances_declaration(decl) for decl in decls]
            )
            return decls
        elif self.debug:
            raise ValueError(f"Unsupported object: {name}")
        else:
            return s.HoleStmt(self.fpos())

    def parse_stmt_block(self, node: TSNode) -> s.Block:
        """
        (function_definition
            name: (identifier)
            parameters: (parameters)
            body: (block))
        """
        name = self.text(node.child_by_field_name("name"))
        body = node.child_by_field_name("body")
        match name:
            case "next" | "control" | "step" | "transition" | "main":
                match body.child(0).type:
                    # ignore while true at the top level of the next block
                    case "while_statement":
                        body = body.child(0)
                        condition = self.parse_expr(
                            body.child_by_field_name("condition")
                        )
                        if isinstance(condition, e.BooleanValue) and condition.value:
                            body = self.search(
                                self.parse_statement, body.child_by_field_name("body")
                            )
                            return s.Block(
                                self.fpos(),
                                [self.parse_statement(stmt) for stmt in body],
                            )
                stmts = self.search(self.parse_statement, body)
                stmts = [self.parse_statement(stmt) for stmt in stmts]
                return s.Block(self.fpos(), stmts)
            case "init" | "start" | "initial":
                stmts = self.search(self.parse_statement, body)
                stmts = [self.parse_statement(stmt) for stmt in stmts]
                return s.Block(self.fpos(), stmts)
            case _ if self.debug:
                raise ValueError(f"Unsupported object: {name}")
            case _:
                return s.HoleStmt(self.fpos())

    def parse_spec_block(self, node: TSNode) -> e.Expression:
        """
        (function_definition
            name: (identifier)
            parameters: (parameters)
            body: (block (return_statement)))
        """
        name = self.text(node.child_by_field_name("name"))
        body = node.child_by_field_name("body").child(0)
        match name:
            case "specification" | "spec" | "specify" | "property" | "properties":
                expressions = self.search(self.parse_expr, body)
                expressions = [self.parse_expr(expr) for expr in expressions]
                if len(expressions) == 0:
                    return e.BooleanValue(self.fpos(), True)
                elif len(expressions) == 1:
                    return expressions[0]
                elif len(expressions) > 1:
                    return e.And(self.fpos(), *expressions)
            case _ if self.debug:
                raise ValueError(f"Unsupported object: {name}")
            case _:
                return e.HoleExpr(self.fpos())

    def parse_control_statement(self, node: TSNode) -> p.Command:
        """
        (call
            function: {self.parse_identifier.__doc__}
            arguments: (argument_list))
        """
        function = self.parse_identifier(node.child_by_field_name("function"))
        arguments = node.child_by_field_name("arguments")
        arguments = self.search(self.parse_integer, arguments)
        arguments = [self.parse_integer(arg) for arg in arguments]
        match function.name.lower():
            case "induction" if len(arguments) <= 1:
                k = 0 if len(arguments) == 0 else arguments[0].value
                return p.Induction(self.fpos(), k)
            case "bmc" | "unroll" if len(arguments) <= 1:
                k = 0 if len(arguments) == 0 else arguments[0].value
                return p.BoundedModelChecking(self.fpos(), k)
            case _ if self.debug:
                raise ValueError(f"Unsupported object: {node.sexp()}")
            case _:
                return p.HoleCmd(self.fpos())

    def parse_control_block(self, node: TSNode) -> p.Block:
        """
        (function_definition
            name: (identifier)
            parameters: (parameters)
            body: (block))
        """
        name = self.text(node.child_by_field_name("name"))
        body = node.child_by_field_name("body")
        if name == "control" or name == "proof":
            stmts = self.search(self.parse_control_statement, body, strict=False)
            stmts = [self.parse_control_statement(stmt) for stmt in stmts]
            return p.Block(self.fpos(), stmts)
        elif self.debug:
            raise ValueError(f"Unsupported object: {name}")
        else:
            return p.HoleCmd(self.fpos())

    def parse_module(self, node: TSNode) -> Module:
        """
        (class_definition
            name: (identifier)
            body: (block))
        """
        name = self.parse_identifier(node.child_by_field_name("name"))
        body = node.child_by_field_name("body")

        def has_name(node: TSNode, name: str) -> bool:
            return self.text(node.child_by_field_name("name")) == name

        type_blocks = [
            b for b in self.search(self.parse_type_block, body) if has_name(b, "types")
        ]
        types = s.Block(
            self.fpos(),
            [t for b in type_blocks for t in self.parse_type_block(b).statements],
        )

        locals_blocks = [
            b for b in self.search(self.parse_var_block, body) if has_name(b, "locals")
        ]
        locals = s.Block(
            self.fpos(),
            [
                v
                for b in locals_blocks
                for v in self.parse_var_block(b, "locals").statements
            ],
        )

        inputs_blocks = [
            b for b in self.search(self.parse_var_block, body) if has_name(b, "inputs")
        ]
        inputs = s.Block(
            self.fpos(),
            [
                v
                for b in inputs_blocks
                for v in self.parse_var_block(b, "inputs").statements
            ],
        )

        outputs_blocks = [
            b for b in self.search(self.parse_var_block, body) if has_name(b, "outputs")
        ]
        outputs = s.Block(
            self.fpos(),
            [
                v
                for b in outputs_blocks
                for v in self.parse_var_block(b, "outputs").statements
            ],
        )

        sharedvars_blocks = [
            b
            for b in self.search(self.parse_var_block, body)
            if has_name(b, "sharedvars")
        ]
        sharedvars = s.Block(
            self.fpos(),
            [
                v
                for b in sharedvars_blocks
                for v in self.parse_var_block(b, "sharedvars").statements
            ],
        )

        instances_blocks = [
            b
            for b in self.search(self.parse_instances_block, body)
            if has_name(b, "instances")
        ]
        instances = s.Block(
            self.fpos(),
            [
                i
                for b in instances_blocks
                for i in self.parse_instances_block(b).statements
            ],
        )

        init_blocks = [
            b
            for b in self.search(self.parse_stmt_block, body)
            if has_name(b, "init") or has_name(b, "start") or has_name(b, "initial")
        ]
        init = s.Block(
            self.fpos(),
            [s for b in init_blocks for s in self.parse_stmt_block(b).statements],
        )

        next_blocks = [
            b
            for b in self.search(self.parse_stmt_block, body)
            if has_name(b, "next")
            or has_name(b, "step")
            or has_name(b, "transition")
            or has_name(b, "main")
            or has_name(b, "control")
        ]
        next = s.Block(
            self.fpos(),
            [s for b in next_blocks for s in self.parse_stmt_block(b).statements],
        )

        spec_blocks = [
            b
            for b in self.search(self.parse_spec_block, body)
            if has_name(b, "specification")
            or has_name(b, "spec")
            or has_name(b, "property")
            or has_name(b, "properties")
        ]
        if len(spec_blocks) == 0:
            spec = e.BooleanValue(self.fpos(), True)
        elif len(spec_blocks) == 1:
            spec = self.parse_spec_block(spec_blocks[0])
        else:
            spec = e.And(self.fpos(), *[self.parse_spec_block(b) for b in spec_blocks])

        control_blocks = [
            b
            for b in self.search(self.parse_control_block, body)
            if has_name(b, "control") or has_name(b, "proof")
        ]
        control = p.Block(
            self.fpos(),
            [s for b in control_blocks for s in self.parse_control_block(b).commands],
        )

        return Module(
            self.fpos(),
            name,
            types,
            locals,
            inputs,
            outputs,
            sharedvars,
            instances,
            init,
            next,
            spec,
            control,
        )
