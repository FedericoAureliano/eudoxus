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
from eudoxus.ast.node import Identifier, Position

RESERVED_STATEMENTS = ["assume", "assert", "havoc"]

PY_LANGUAGE = TSLanguage(ts.language(), "python")


def ts_search(query: str, node: TSNode) -> List[TSNode]:
    query = query + " @target"
    matches = PY_LANGUAGE.query(query).matches(node)
    return [m[1]["target"] for m in matches]


def pos(node: TSNode) -> Position:
    return Position(node.start_byte)


class Parser:
    def __init__(self, src):
        parser = TSParser()
        parser.set_language(PY_LANGUAGE)

        def read_callable_byte_offset(byte_offset, _):
            return src[byte_offset : byte_offset + 1]

        self.text = lambda node: src[node.start_byte : node.end_byte].decode("utf-8")

        self.tree = parser.parse(read_callable_byte_offset)

        self.enum_count = 0

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
        return self._search(to_search, node, strict=strict)

    def _search(self, query, node: TSNode, strict=True) -> List[TSNode]:
        """
        Returns a list of nodes that match the query in the docstring of the function.
        This is a trick to be able to use docstrings as queries (preconditions)

        params:
            func: a function whose docstring contains the query
            node: the node to search in
            strict: if True, only return nodes that are direct children of the node
        """
        while "{" in query:
            query = f'f"""{query}"""'
            query = eval(query)
        results = ts_search(query, node)
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
            case _:
                raise ValueError(f"Unsupported object: {node.sexp()}")

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

            case _:
                raise ValueError(
                    f"Unsupported object: {node.sexp()}\n{self.text(node)}"
                )

    def type_helper(self, id: Identifier, args: TSNode) -> t.Type:
        p = id.position
        name = id.name
        if "bool" in name.lower():
            return t.Boolean(p)
        elif "int" in name.lower():
            return t.Integer(p)
        elif "float" in name.lower():
            return t.Float(p)
        elif "bv" in name.lower() or "bitvector" in name.lower():
            size = self.search(self.parse_integer, args)[0]
            size = self.parse_integer(size).value
            return t.BitVector(p, size)
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
            else:
                raise ValueError(f"Unsupported object: {self.text(args)}")
            return t.Array(p, index_t, elem_t)
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
            return t.Enumeration(p, args_list)
        else:
            return t.Synonym(p, id)

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
            case _:
                raise ValueError(
                    f"Unsupported object: {node.sexp()}, \n{self.text(node)}"
                )

    def parse_type_declaration(self, node: TSNode) -> s.Type:
        """
        (assignment
            left: {self.parse_identifier.__doc__}
            right: {self.parse_type_expr.__doc__})
        """
        id = self.parse_identifier(node.child_by_field_name("left"))
        rhs = self.parse_type_expr(node.child_by_field_name("right"))
        if isinstance(rhs, t.Enumeration):
            fst = rhs.values[0]
            if fst.name == id.name:
                # e.g., self.t = Enum('t', 'A', 'B', 'C')
                rhs = t.Enumeration(rhs.position, rhs.values[1:])

        return s.Type(pos(node), id, rhs)

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

    def expr_helper(
        self, pos: Position, f: str, args: List[e.Expression]
    ) -> e.Expression:
        match f.lower():
            case "bitvector" | "bv" | "bitvec":
                match args:
                    case [e.Integer(_, value), e.Integer(_, size)]:
                        return e.BitVector(pos, value, size)
                    case _:
                        raise ValueError(f"Unsupported args: {args}")
            case "and" | "conjunct" | "conjunction":
                return e.Application(pos, e.And(pos), args)
            case "or" | "disjunct" | "disjunction":
                return e.Application(pos, e.Or(pos), args)
            case "implies" | "impl":
                return e.Application(pos, e.Implies(pos), args)
            case "iff" | "equiv" | "eq" | "equal":
                return e.Application(pos, e.Equal(pos), args)
            case "not" | "neg":
                return e.Application(pos, e.Not(pos), args)
            case "add" | "plus" | "sum" | "addition":
                return e.Application(pos, e.Add(pos), args)
            case "sub" | "subtract" | "minus":
                return e.Application(pos, e.Subtract(pos), args)
            case "mul" | "multiply" | "times":
                return e.Application(pos, e.Multiply(pos), args)
            case "div" | "divide" | "quotient":
                return e.Application(pos, e.Divide(pos), args)
            case "mod" | "modulo" | "remainder" | "modulus":
                return e.Application(pos, e.Modulo(pos), args)
            case "neq" | "notequal":
                return e.Application(pos, e.NotEqual(pos), args)
            case "lt" | "lessthan":
                return e.Application(pos, e.LessThan(pos), args)
            case "le" | "lte" | "lessthanorequal":
                return e.Application(pos, e.LessThanOrEqual(pos), args)
            case "gt" | "greaterthan":
                return e.Application(pos, e.GreaterThan(pos), args)
            case "ge" | "gte" | "greaterthanorequal":
                return e.Application(pos, e.GreaterThanOrEqual(pos), args)
            case "select" | "sel":
                return e.Application(pos, e.Selection(pos), args)
            case "ite" | "ifthenelse" | "ifelse" | "if" | "if_":
                return e.Application(pos, e.Ite(pos), args)
            case _:
                return e.Application(pos, Identifier(pos, f), args)

    def parse_app_expr(self, node: TSNode) -> e.Application:
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
                quant = (
                    e.Forall(pos(node), bindings)
                    if function.name == "forall"
                    else e.Exists(pos(node), bindings)
                )
                return e.Application(pos(node), quant, [body])
            case _:
                arguments = parse_args()
                return self.expr_helper(pos(node), function.name, arguments)

    def parse_app_of_app_expr(self, node: TSNode) -> e.Application:
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

    def parse_select_expr(self, node: TSNode) -> e.Selection:
        """
        (attribute
            object: (_)
            attribute: (_))
        """
        p = pos(node)
        record = self.parse_expr(node.child_by_field_name("object"))
        selector = self.parse_identifier(node.child_by_field_name("attribute"))
        return e.Selection(p, record, selector)

    def parse_boolean_expression(self, node: TSNode) -> e.Application:
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
                return e.Application(p, e.And(p), [left, right])
            case "or":
                return e.Application(p, e.Or(p), [left, right])
            case "not":
                return e.Application(p, e.Not(p), [left])
            case _:
                raise ValueError(f"Unsupported object: {node.sexp()}")

    def parse_comparison_expression(self, node: TSNode) -> e.Application:
        """
        (comparison_operator)
        """
        p = pos(node)
        args = self.search(self.parse_expr, node)
        args = [self.parse_expr(arg) for arg in args]
        match self.text(node.child(1)):
            case "==":
                return e.Application(p, e.Equal(p), args)
            case "!=":
                return e.Application(p, e.NotEqual(p), args)
            case "<":
                return e.Application(p, e.LessThan(p), args)
            case ">":
                return e.Application(p, e.GreaterThan(p), args)
            case "<=":
                return e.Application(p, e.LessThanOrEqual(p), args)
            case ">=":
                return e.Application(p, e.GreaterThanOrEqual(p), args)
            case _:
                raise ValueError(f"Unsupported object: {node.sexp()}")

    def parse_binary_expression(self, node: TSNode) -> e.Application:
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
                return e.Application(p, e.Add(p), [left, right])
            case "-":
                return e.Application(p, e.Subtract(p), [left, right])
            case "*":
                return e.Application(p, e.Multiply(p), [left, right])
            case "/":
                return e.Application(p, e.Divide(p), [left, right])
            case _:
                raise ValueError(
                    f"Unsupported object: {node.sexp()},"
                    + f" {self.text(node.child_by_field_name('operator'))}"
                )

    def parse_integer(self, node: TSNode) -> e.Constant:
        """(integer)"""
        return e.Integer(pos(node), int(self.text(node)))

    def parse_string(self, node: TSNode) -> str:
        """(string)"""
        return self.text(node)[1:-1]

    def parse_variant(self, node: TSNode) -> e.Constant:
        """(string)"""
        return e.Variant(pos(node), self.parse_string(node))

    def parse_expr(self, node: TSNode) -> e.Expression:
        """
        [
            {self.parse_flat_identifier.__doc__}
            {self.parse_self_identifier.__doc__}
            {self.parse_variant.__doc__}
            {self.parse_select_expr.__doc__}
            {self.parse_app_expr.__doc__}
            {self.parse_app_of_app_expr.__doc__}
            {self.parse_binary_expression.__doc__}
            {self.parse_comparison_expression.__doc__}
            {self.parse_boolean_expression.__doc__}
            {self.parse_integer.__doc__}
        ]
        """

        match node.type:
            case "identifier":
                id = self.parse_flat_identifier(node)
                return e.Application(id.position, id, [])
            case "attribute" if self.text(node.child_by_field_name("object")) == "self":
                id = self.parse_self_identifier(node)
                return e.Application(id.position, id, [])
            case "attribute":
                return self.parse_select_expr(node)
            case "call" if node.child_by_field_name("function").type == "call":
                return self.parse_app_of_app_expr(node)
            case "call":
                return self.parse_app_expr(node)
            case "binary_operator":
                return self.parse_binary_expression(node)
            case "comparison_operator":
                return self.parse_comparison_expression(node)
            case "boolean_operator":
                return self.parse_boolean_expression(node)
            case "integer":
                return self.parse_integer(node)
            case "string":
                return self.parse_variant(node)
            case _:
                raise ValueError(
                    f"Unsupported object: {node.sexp()} of type {node.type}"
                )

    def parse_var_declaration(self, node: TSNode, kind: str) -> s.Variable:
        """
        (assignment
            left: {self.parse_identifier.__doc__}
            right: {self.parse_type_expr.__doc__})
        """
        id = self.parse_identifier(node.child_by_field_name("left"))
        rhs = self.parse_type_expr(node.child_by_field_name("right"))
        match kind:
            case "locals":
                return s.Local(pos(node), id, rhs)
            case "inputs":
                return s.Input(pos(node), id, rhs)
            case "outputs":
                return s.Output(pos(node), id, rhs)
            case "sharedvars":
                return s.SharedVar(pos(node), id, rhs)
            case _:
                raise ValueError(f"Unsupported object: {kind}")

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

    def parse_instances_declaration(self, node: TSNode) -> s.Instance:
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
        return s.Instance(pos(node), target, mod, args)

    def parse_assignment(self, node: TSNode) -> s.Assignment:
        """
        (expression_statement
            (assignment
                left: {self.parse_identifier.__doc__}
                right: {self.parse_expr.__doc__}))
        """
        node = node.child(0)
        lhs = self.parse_identifier(node.child_by_field_name("left"))
        rhs = self.parse_expr(node.child_by_field_name("right"))
        return s.Assignment(pos(node), lhs, rhs)

    def parse_if_statement(self, node: TSNode) -> s.If:
        """
        (if_statement
            condition: (expression)
            consequence: (block)
            alternative:
                (else_clause
                    body: (block))?)
        """
        condition = self.parse_expr(node.child_by_field_name("condition"))
        consequence = self.search(
            self.parse_statement, node.child_by_field_name("consequence")
        )
        consequence = s.Block(
            pos(node), [self.parse_statement(stmt) for stmt in consequence]
        )
        alternative = node.child_by_field_name("alternative")
        if alternative is None:
            return s.If(pos(node), condition, consequence, s.Block(pos(node), []))
        else:
            # get the else clause (first two children are "else" and ":")
            alternative = alternative.child_by_field_name("body")
            alternative = self.search(self.parse_statement, alternative)
            alternative = s.Block(
                pos(node), [self.parse_statement(stmt) for stmt in alternative]
            )
            return s.If(pos(node), condition, consequence, alternative)

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
            case _:
                raise ValueError(f"Unsupported object: {node.sexp()}")

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
            case _:
                raise ValueError(f"Unsupported object: {node.sexp()}")

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
            case "expression_statement":
                return self.parse_assignment(node)
            case _:
                raise ValueError(f"Unsupported object: {node.sexp()}")

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
            case _:
                raise ValueError(f"Unsupported object: {name}")

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
        else:
            raise ValueError(f"Unsupported object: {name}")

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
        else:
            raise ValueError(f"Unsupported object: {name}")

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
            case _:
                raise ValueError(f"Unsupported object: {name}")

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
            case "specification":
                expressions = self.search(self.parse_expr, body)
                expressions = [self.parse_expr(expr) for expr in expressions]
                if len(expressions) == 0:
                    return e.Boolean(pos(node), True)
                elif len(expressions) == 1:
                    return expressions[0]
                elif len(expressions) > 1:
                    return e.Application(pos(node), e.And(pos(node)), expressions)
            case _:
                raise ValueError(f"Unsupported object: {name}")

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
            case _:
                raise ValueError(f"Unsupported object: {node.sexp()}")

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
        else:
            raise ValueError(f"Unsupported object: {name}")

    def parse_module(self, node: TSNode) -> Module:
        """
        (class_definition
            name: (identifier)
            body: (block))
        """
        name = self.parse_identifier(node.child_by_field_name("name"))
        body = node.child_by_field_name("body")
        pn = pos(node)

        def has_name(node: TSNode, name: str) -> bool:
            return self.text(node.child_by_field_name("name")) == name

        type_blocks = [
            b for b in self.search(self.parse_type_block, body) if has_name(b, "types")
        ]
        types = s.Block(
            pn, [t for b in type_blocks for t in self.parse_type_block(b).statements]
        )

        locals_blocks = [
            b for b in self.search(self.parse_var_block, body) if has_name(b, "locals")
        ]
        locals = s.Block(
            pn,
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
            pn,
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
            pn,
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
            pn,
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
            pn,
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
            pn, [s for b in init_blocks for s in self.parse_stmt_block(b).statements]
        )

        next_blocks = [
            b for b in self.search(self.parse_stmt_block, body) if has_name(b, "next")
        ]
        next = s.Block(
            pn, [s for b in next_blocks for s in self.parse_stmt_block(b).statements]
        )

        spec_blocks = [
            b
            for b in self.search(self.parse_spec_block, body)
            if has_name(b, "specification")
        ]
        if len(spec_blocks) == 0:
            spec = e.Boolean(pn, True)
        elif len(spec_blocks) == 1:
            spec = self.parse_spec_block(spec_blocks[0])
        else:
            spec = e.Application(
                pn, e.And(pn), [self.parse_spec_block(b) for b in spec_blocks]
            )

        control_blocks = [
            b
            for b in self.search(self.parse_control_block, body)
            if has_name(b, "control") or has_name(b, "proof")
        ]
        control = p.Block(
            pn,
            [s for b in control_blocks for s in self.parse_control_block(b).commands],
        )

        return Module(
            pn,
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
