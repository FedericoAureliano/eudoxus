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


def pos(node: TSNode) -> Position:
    return Position(node.id)


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
        self.position_count = -1

    def fresh_pos(self) -> Position:
        self.position_count -= 1
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
        return Identifier(pos(node), self.text(node))

    def parse_self_identifier(self, node: TSNode) -> Identifier:
        """
        (attribute
            object: (identifier)
            attribute: (identifier))
        """
        object = self.text(node.child_by_field_name("object"))
        match object:
            case "self":
                return Identifier(
                    pos(node), self.text(node.child_by_field_name("attribute"))
                )
            case _ if self.debug:
                raise ValueError(f"Unsupported object: {node.sexp()}")
            case _:
                return HoleId(pos(node))

    def parse_identifier(self, node: TSNode) -> Identifier:
        """
        [
            {self.parse_flat_identifier.__doc__}
            {self.parse_self_identifier.__doc__}
        ]
        """
        match node.type:
            case "identifier":
                return self.parse_flat_identifier(node)
            case "attribute":
                return self.parse_self_identifier(node)
            case _ if self.debug:
                raise ValueError(f"Unsupported object: {node.sexp()}")
            case _:
                return HoleId(pos(node))

    def type_helper(self, id: Identifier, args: TSNode) -> t.Type:
        p = id.position
        name = id.name
        if "bool" in name.lower():
            return t.BooleanType(p)
        elif "int" in name.lower():
            return t.IntegerType(p)
        elif "real" in name.lower():
            return t.RealType(p)
        elif "bv" in name.lower() or "bitvector" in name.lower():
            size = self.search(self.parse_integer, args)[0]
            size = self.parse_integer(size).value
            return t.BitVectorType(p, size)
        elif "arr" in name.lower():
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
                return t.HoleType(p)
            return t.ArrayType(p, index_t, elem_t)
        elif "enum" in name.lower():
            if (
                args.child_count >= 3
                and args.child(1).type == "string"
                and args.child(3).type == "list"
            ):
                # e.g., Enum('t', ['B', 'C'])
                args = args.child(3)

            args_list = self.search(self.parse_string, args, strict=False)
            args_list = [
                Identifier(pos(arg), self.parse_string(arg)) for arg in args_list
            ]

            if len(args_list) == 0:
                args_list = self.search(self.parse_integer, args, strict=False)
                args_list = [self.parse_integer(arg) for arg in args_list]
                k = args_list[0]
                args_list = []
                for _ in range(k.value):
                    args_list.append(Identifier(p, "anon_enum_" + str(self.enum_count)))
                    self.enum_count += 1
            return t.EnumeratedType(p, args_list)
        elif "record" in name.lower():
            fields = self.search(self.parse_string_type_pair, args, strict=False)
            fields = [self.parse_string_type_pair(field) for field in fields]
            return t.RecordType(p, fields)
        else:
            return t.SynonymType(p, id)

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
                return self.type_helper(self.parse_identifier(node), [])
            case "call":
                return self.parse_app_type(node)
            case _ if self.debug:
                raise ValueError(f"Unsupported object: {node.sexp()}")
            case _:
                return t.HoleType(pos(node))

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
                rhs = t.EnumeratedType(rhs.position, rhs.values[1:])

        return s.TypeDecl(pos(node), id, rhs)

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
        id = Identifier(pos(node.child(1)), id)
        ty = self.parse_type_expr(node.child(3))
        return (id, ty)

    def expr_helper(
        self, pos: Position, f: str, args: List[e.Expression]
    ) -> e.Expression:
        match f.lower():
            case bv if "bv" in bv or "bitvec" in bv:
                match args:
                    case [e.IntegerValue(_, value), e.IntegerValue(_, size)]:
                        return e.BitVectorValue(pos, value, size)
                    case _ if self.debug:
                        raise ValueError(f"Unsupported args: {args}")
                    case _:
                        return e.HoleExpr(pos)
            case "not" | "neg" if len(args) == 1:
                return e.Not(pos, *args)
            case "neg" | "negative" | "negate" if len(args) == 1:
                return e.Negate(pos, *args)
            case _ if not self.debug and len(args) == 1:
                # unary but none of the above, just return the arg
                return args[0]
            case "and" | "conjunct" | "conjunction" if len(args) == 2:
                return e.And(pos, *args)
            case "or" | "disjunct" | "disjunction" if len(args) == 2:
                return e.Or(pos, *args)
            case "implies" | "impl" if len(args) == 2:
                return e.Implies(pos, *args)
            case "iff" | "equiv" | "eq" | "equal" if len(args) == 2:
                return e.Equal(pos, *args)
            case "add" | "plus" | "sum" | "addition" if len(args) == 2:
                return e.Add(pos, *args)
            case "sub" | "subtract" | "minus" if len(args) == 2:
                return e.Subtract(pos, *args)
            case "mul" | "multiply" | "times" if len(args) == 2:
                return e.Multiply(pos, *args)
            case "div" | "divide" | "quotient" if len(args) == 2:
                return e.Divide(pos, *args)
            case "mod" | "modulo" | "remainder" | "modulus" if len(args) == 2:
                return e.Modulo(pos, *args)
            case "neq" | "notequal" if len(args) == 2:
                return e.NotEqual(pos, *args)
            case "lt" | "lessthan" if len(args) == 2:
                return e.LessThan(pos, *args)
            case "le" | "lte" | "lessthanorequal" if len(args) == 2:
                return e.LessThanOrEqual(pos, *args)
            case "gt" | "greaterthan" if len(args) == 2:
                return e.GreaterThan(pos, *args)
            case "ge" | "gte" | "greaterthanorequal" if len(args) == 2:
                return e.GreaterThanOrEqual(pos, *args)
            case "select" | "sel" if len(args) == 2:
                return e.RecordSelect(pos, *args)
            case "ite" | "ifthenelse" | "ifelse" | "if" | "if_" if len(args) == 3:
                return e.Ite(pos, *args)
            case _ if self.debug:
                raise ValueError(f"Unsupported function: {f}")
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
            return arguments

        fnode = node.child_by_field_name("function")
        function = self.parse_identifier(fnode)
        match function.name.lower():
            case "forall" | "exists":
                arguments = node.child_by_field_name("arguments")
                bindings = arguments.child(1)
                bindings = self.search(
                    self.parse_name_type_pair, bindings, strict=False
                )
                bindings = [self.parse_name_type_pair(binding) for binding in bindings]
                body = arguments.child(3)
                body = self.parse_expr(body)
                if function.name == "forall":
                    return foldl(
                        lambda x, y: e.Forall(pos(node), *x, y),
                        e.Forall(pos(node), *bindings[0], body),
                        bindings[1:],
                    )
                else:
                    return foldl(
                        lambda x, y: e.Exists(pos(node), *x, y),
                        e.Exists(pos(node), *bindings[0], body),
                        bindings[1:],
                    )
            case _:
                arguments = parse_args()
                return self.expr_helper(pos(node), function.name, arguments)

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
        return self.expr_helper(pos(node), function.name, arguments)

    def parse_subscript_expr(self, node: TSNode) -> e.ArraySelect:
        """
        (subscript
            value: (_)
            subscript: (_))
        """
        array = self.parse_expr(node.child_by_field_name("value"))
        index = self.parse_expr(node.child_by_field_name("subscript"))
        return e.ArraySelect(pos(node), array, index)

    def parse_select_expr(self, node: TSNode) -> e.RecordSelect:
        """
        (attribute
            object: (_)
            attribute: (_))
        """
        p = pos(node)
        record = self.parse_expr(node.child_by_field_name("object"))
        selector = self.parse_identifier(node.child_by_field_name("attribute"))
        return e.RecordSelect(p, record, selector)

    def parse_boolean_expression(self, node: TSNode) -> e.Expression:
        """
        (boolean_operator
            left: (_)
            right: (_))
        """
        p = pos(node)
        left = self.parse_expr(node.child_by_field_name("left"))
        right = self.parse_expr(node.child_by_field_name("right"))
        match self.text(node.child_by_field_name("operator")):
            case "and":
                return e.And(p, left, right)
            case "or":
                return e.Or(p, left, right)
            case "not":
                return e.Not(p, left)
            case _ if self.debug:
                raise ValueError(f"Unsupported object: {node.sexp()}")
            case _:
                return e.HoleExpr(p)

    def parse_comparison_expression(self, node: TSNode) -> e.Expression:
        """
        (comparison_operator)
        """
        p = pos(node)
        args = self.search(self.parse_expr, node)
        args = [self.parse_expr(arg) for arg in args]
        match self.text(node.child(1)):
            case "==":
                base = e.Equal(p, *args[:2])
                for i, arg in enumerate(args):
                    if i > 1:
                        base = e.And(p, base, e.Equal(p, args[i - 1], arg))
                return base
            case "!=":
                base = e.NotEqual(p, *args[:2])
                for i, arg in enumerate(args):
                    if i > 1:
                        base = e.And(p, base, e.NotEqual(p, args[i - 1], arg))
                return base
            case "<":
                base = e.LessThan(p, *args[:2])
                for i, arg in enumerate(args):
                    if i > 1:
                        base = e.And(p, base, e.LessThan(p, args[i - 1], arg))
                return base
            case ">":
                base = e.GreaterThan(p, *args[:2])
                for i, arg in enumerate(args):
                    if i > 1:
                        base = e.And(p, base, e.GreaterThan(p, args[i - 1], arg))
                return base
            case "<=":
                base = e.LessThanOrEqual(p, *args[:2])
                for i, arg in enumerate(args):
                    if i > 1:
                        base = e.And(p, base, e.LessThanOrEqual(p, args[i - 1], arg))
                return base
            case ">=":
                base = e.GreaterThanOrEqual(p, *args[:2])
                for i, arg in enumerate(args):
                    if i > 1:
                        base = e.And(p, base, e.GreaterThanOrEqual(p, args[i - 1], arg))
                return base
            case _ if self.debug:
                raise ValueError(f"Unsupported object: {node.sexp()}")
            case _:
                return e.HoleExpr(p)

    def parse_unary_expression(self, node: TSNode) -> e.Expression:
        """
        (unary_operator)
        """
        p = pos(node)
        arg = self.parse_expr(node.child_by_field_name("argument"))
        match self.text(node.child_by_field_name("operator")):
            case "-":
                return e.Negate(p, arg)
            case _ if self.debug:
                raise ValueError(f"Unsupported object: {node.sexp()}")
            case _:
                return e.HoleExpr(p)

    def parse_not_expression(self, node: TSNode) -> e.Expression:
        """
        (not_operator)
        """
        p = pos(node)
        arg = self.parse_expr(node.child_by_field_name("argument"))
        return e.Not(p, arg)

    def parse_binary_expression(self, node: TSNode) -> e.Expression:
        """
        (binary_operator
            left: (_)
            right: (_))
        """
        p = pos(node)
        left = self.parse_expr(node.child_by_field_name("left"))
        right = self.parse_expr(node.child_by_field_name("right"))
        match self.text(node.child_by_field_name("operator")):
            case "+":
                return e.Add(p, left, right)
            case "-":
                return e.Subtract(p, left, right)
            case "*":
                return e.Multiply(p, left, right)
            case "/":
                return e.Divide(p, left, right)
            case "%":
                return e.Modulo(p, left, right)
            case _ if self.debug:
                raise ValueError(f"Unsupported object: {node.sexp()}")
            case _:
                return e.HoleExpr(p)

    def parse_integer(self, node: TSNode) -> e.Value:
        """(integer)"""
        return e.IntegerValue(pos(node), int(self.text(node)))

    def parse_float(self, node: TSNode) -> e.Value:
        """(float)"""
        return e.RealValue(pos(node), float(self.text(node)))

    def parse_boolean(self, node: TSNode) -> e.Value:
        """
        [
            (true)
            (false)
        ]
        """
        return e.BooleanValue(pos(node), self.text(node) == "True")

    def parse_string(self, node: TSNode) -> str:
        """(string)"""
        return self.text(node)[1:-1]

    def parse_variant(self, node: TSNode) -> e.Value:
        """(string)"""
        return e.EnumValue(pos(node), self.parse_string(node))

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
            (true)
            (false)
            {self.parse_integer.__doc__}
            {self.parse_float.__doc__}
            (parenthesized_expression)
        ]
        """
        match node.type:
            case "identifier":
                id = self.parse_flat_identifier(node)
                return e.FunctionApplication(id.position, id, [])
            case "attribute" if self.text(node.child_by_field_name("object")) == "self":
                id = self.parse_self_identifier(node)
                return e.FunctionApplication(id.position, id, [])
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
                return e.HoleExpr(pos(node))

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
                return s.LocalDecl(pos(node), id, rhs)
            case "inputs":
                return s.InputDecl(pos(node), id, rhs)
            case "outputs":
                return s.OutputDecl(pos(node), id, rhs)
            case "sharedvars":
                return s.SharedDecl(pos(node), id, rhs)
            case _ if self.debug:
                raise ValueError(f"Unsupported object: {kind}")
            case _:
                return s.LocalDecl(pos(node), id, rhs)

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
        return s.InstanceDecl(pos(node), target, mod, args)

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
                rhs = e.ArrayStore(pos(node), array, index, rhs)
        return s.Assignment(pos(node), lhs, rhs)

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
                rhs = e.Add(pos(node), lhs, rhs)
            case "-=":
                rhs = e.Subtract(pos(node), lhs, rhs)
            case "*=":
                rhs = e.Multiply(pos(node), lhs, rhs)
            case "/=":
                rhs = e.Divide(pos(node), lhs, rhs)
            case "%=":
                rhs = e.Modulo(pos(node), lhs, rhs)
            case _ if self.debug:
                raise ValueError(f"Unsupported object: {node.sexp()}")
            case _:
                return s.HoleStmt(pos(node))
        return s.Assignment(pos(node), lhs, rhs)

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
            pos(node), [self.parse_statement(stmt) for stmt in consequence]
        )
        return (condition, consequence)

    def parse_else(self, node: TSNode) -> s.Block:
        """
        (else_clause
            body: (_))
        """
        body = self.search(self.parse_statement, node.child_by_field_name("body"))
        body = s.Block(pos(node), [self.parse_statement(stmt) for stmt in body])
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
            pos(node), [self.parse_statement(stmt) for stmt in consequence]
        )
        elifs = self.search(self.parse_elif, node)
        elifs = [self.parse_elif(elif_) for elif_ in elifs][::-1]
        else_ = self.search(self.parse_else, node)
        if len(else_) != 1:
            else_ = s.Block(pos(node), [])
        else:
            else_ = self.parse_else(else_[0])

        inner = foldl(
            lambda acc, x: s.Block(
                x[0].position, [s.If(x[0].position, x[0], x[1], acc)]
            ),
            else_,
            elifs,
        )
        return s.If(pos(node), condition, consequence, inner)

    def parse_havoc_statement(self, node: TSNode) -> s.Havoc:
        """
        (expression_statement
            (call
                function: (identifier)
                arguments: (argument_list)))
        """
        call = node.child(0)
        function = self.parse_identifier(call.child_by_field_name("function"))
        args = call.child_by_field_name("arguments")
        args = self.search(self.parse_identifier, args)
        args = [self.parse_identifier(arg) for arg in args]
        match function.name:
            case "havoc" if len(args) == 1:
                return s.Havoc(pos(node), args[0])
            case _ if self.debug:
                raise ValueError(f"Unsupported object: {node.sexp()}")
            case _:
                return s.HoleStmt(pos(node))

    def parse_assume_statement(self, node: TSNode) -> s.Assume:
        """
        (expression_statement
            (call
                function: (identifier)
                arguments: (argument_list)))
        """
        call = node.child(0)
        function = self.parse_identifier(call.child_by_field_name("function"))
        args = call.child_by_field_name("arguments")
        args = self.search(self.parse_expr, args)
        args = [self.parse_expr(arg) for arg in args]
        match function.name:
            case "assume" if len(args) == 1:
                return s.Assume(pos(node), args[0])
            case _ if self.debug:
                raise ValueError(f"Unsupported object: {node.sexp()}")
            case _:
                return s.HoleStmt(pos(node))

    def parse_assert_statement(self, node: TSNode) -> s.Assert:
        """
        (assert_statement)
        """
        condition = node.child(1)
        condition = self.parse_expr(condition)
        return s.Assert(pos(node), condition)

    def parse_statement(self, node: TSNode) -> s.Statement:
        """
        [
            {self.parse_assignment.__doc__}
            {self.parse_augmented_assignment.__doc__}
            {self.parse_if_statement.__doc__}
            {self.parse_assert_statement.__doc__}
            {self.parse_assume_statement.__doc__}
            {self.parse_havoc_statement.__doc__}
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
            case "expression_statement":
                return self.parse_assignment(node)
            case _ if self.debug:
                raise ValueError(f"Unsupported object: {node.sexp()}")
            case _:
                return s.HoleStmt(pos(node))

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
                    pos(node), [self.parse_type_declaration(decl) for decl in decls]
                )
                return decls
            case _ if self.debug:
                raise ValueError(f"Unsupported object: {name}")
            case _:
                return s.HoleStmt(pos(node))

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
                pos(node), [self.parse_var_declaration(decl, kind) for decl in decls]
            )
            return decls
        elif self.debug:
            raise ValueError(f"Unsupported object: {name}")
        else:
            return s.HoleStmt(pos(node))

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
                pos(node), [self.parse_instances_declaration(decl) for decl in decls]
            )
            return decls
        elif self.debug:
            raise ValueError(f"Unsupported object: {name}")
        else:
            return s.HoleStmt(pos(node))

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
            case "init" | "next":
                stmts = self.search(self.parse_statement, body)
                stmts = [self.parse_statement(stmt) for stmt in stmts]
                return s.Block(pos(node), stmts)
            case _ if self.debug:
                raise ValueError(f"Unsupported object: {name}")
            case _:
                return s.HoleStmt(pos(node))

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
                    return e.BooleanValue(pos(node), True)
                elif len(expressions) == 1:
                    return expressions[0]
                elif len(expressions) > 1:
                    return e.And(pos(node), *expressions)
            case _ if self.debug:
                raise ValueError(f"Unsupported object: {name}")
            case _:
                return e.HoleExpr(pos(node))

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
                return p.Induction(pos(node), k)
            case "bmc" | "unroll" if len(arguments) <= 1:
                k = 0 if len(arguments) == 0 else arguments[0].value
                return p.BoundedModelChecking(pos(node), k)
            case _ if self.debug:
                raise ValueError(f"Unsupported object: {node.sexp()}")
            case _:
                return p.HoleCmd(pos(node))

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
            return p.Block(pos(node), stmts)
        elif self.debug:
            raise ValueError(f"Unsupported object: {name}")
        else:
            return p.HoleCmd(pos(node))

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
            self.fresh_pos(),
            [t for b in type_blocks for t in self.parse_type_block(b).statements],
        )

        locals_blocks = [
            b for b in self.search(self.parse_var_block, body) if has_name(b, "locals")
        ]
        locals = s.Block(
            self.fresh_pos(),
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
            self.fresh_pos(),
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
            self.fresh_pos(),
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
            self.fresh_pos(),
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
            self.fresh_pos(),
            [
                i
                for b in instances_blocks
                for i in self.parse_instances_block(b).statements
            ],
        )

        init_blocks = [
            b for b in self.search(self.parse_stmt_block, body) if has_name(b, "init")
        ]
        init = s.Block(
            self.fresh_pos(),
            [s for b in init_blocks for s in self.parse_stmt_block(b).statements],
        )

        next_blocks = [
            b for b in self.search(self.parse_stmt_block, body) if has_name(b, "next")
        ]
        next = s.Block(
            self.fresh_pos(),
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
            spec = e.BooleanValue(self.fresh_pos(), True)
        elif len(spec_blocks) == 1:
            spec = self.parse_spec_block(spec_blocks[0])
        else:
            spec = e.And(
                self.fresh_pos(), *[self.parse_spec_block(b) for b in spec_blocks]
            )

        control_blocks = [
            b
            for b in self.search(self.parse_control_block, body)
            if has_name(b, "control") or has_name(b, "proof")
        ]
        control = p.Block(
            self.fresh_pos(),
            [s for b in control_blocks for s in self.parse_control_block(b).commands],
        )

        return Module(
            pos(node),
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
