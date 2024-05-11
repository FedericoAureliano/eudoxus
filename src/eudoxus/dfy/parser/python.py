from tree_sitter import Node as TSNode

import eudoxus.ast.statement as s
from eudoxus.ast.node import Hole, Position
from eudoxus.ast.type import Boolean, Float, Integer, Type
from eudoxus.dfy.ast.list import List
from eudoxus.dfy.ast.module import DfyModule
from eudoxus.dfy.ast.params import Param, Params
from eudoxus.dfy.ast.statement import Comment, Ensures, Requires, Return
from eudoxus.parser.python import Parser, pos


class DfyParser(Parser):
    def parse_simple_type(self, node: TSNode) -> Type:
        """
        (type (identifier))
        """
        if self.text(node) == "int":
            return Integer(pos(node))
        elif self.text(node) == "bool":
            return Boolean(pos(node))
        elif self.text(node) == "float":
            return Float(pos(node), "float")
        else:
            raise NotImplementedError

    def parse_type(self, node: TSNode) -> Type:
        # case where it's a simple type

        if node.children[0].type == "generic_type":
            match self.text(node.children[0].children[0]):
                case "List":
                    return List(
                        pos(node.children[0].children[0]),
                        self.parse_type(node.children[0].children[1].children[1]),
                    )
                case _:
                    raise NotImplementedError

        return self.parse_simple_type(node.children[0])

    def has_name(self, node: TSNode, name: str) -> bool:
        return self.text(node.child_by_field_name("name")) == name

    def parse_typed_parameter(self, node: TSNode, typed=True) -> Param:
        """
        (typed_parameter (identifier) type: (type (_)))
        """

        name = self.parse_identifier(node.children[0])
        type = self.parse_type(node.child_by_field_name("type"))
        return Param(pos(node), type, name)

    def parse_untyped_parameter(self, node: TSNode) -> Param:
        """(identifier)"""
        return Param(
            pos(node), Hole(Position(node.end_byte)), self.parse_identifier(node)
        )

    def parse_parameters(self, node: TSNode) -> Params:
        # hard parse because I need to handle the cases of (identifier) when untyped
        typed_param_list = [b for b in self.search(self.parse_typed_parameter, node)]
        params = [self.parse_typed_parameter(param) for param in typed_param_list]

        untyped_param_list = [c for c in node.children if c.type == "identifier"]
        params = params + [self.parse_untyped_parameter(p) for p in untyped_param_list]
        return Params(pos(node), params)

    def parse_return_statement(self, node: TSNode) -> Return:
        """
        (return_statement (_))
        """
        return Return(pos(node), self.parse_expr(node.children[1]))

    def parse_statement(self, node: TSNode) -> s.Statement:
        """
        [
            {self.parse_assignment.__doc__}
            {self.parse_if_statement.__doc__}
            {self.parse_assert_statement.__doc__}
            {self.parse_assume_statement.__doc__}
            {self.parse_havoc_statement.__doc__}
            {self.parse_ensures_statement.__doc__}
            {self.parse_requires_statement.__doc__}
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
            return reserved.lower() in [
                "dafnypy.requires",
                "dafnypy.ensures",
                "assert",
                "havoc",
            ]

        match node.type:
            case "if_statement":
                return self.parse_if_statement(node)
            case "assert_statement":
                return self.parse_assert_statement(node)
            case "expression_statement" if is_reserved(get_func_name(node)):
                reserved = get_func_name(node)
                match reserved:
                    case "dafnypy.ensures":
                        return self.parse_ensures_statement(node)
                    case "dafnypy.requires":
                        return self.parse_requires_statement(node)
                    case "havoc":
                        return self.parse_havoc_statement(node)
            case "expression_statement":
                return self.parse_assignment(node)
            case "return_statement":
                return self.parse_return_statement(node)
            case "comment":
                return self.parse_comment(node)

            case _:
                raise ValueError(f"Unsupported object: {node.sexp()}")

    def parse_comment(self, node: TSNode) -> None:
        return Comment(pos(node), self.text(node))

    def parse_requires_statement(self, node: TSNode) -> Requires:
        """
        (expression_statement
            (call
                function: (attribute object: (identifier) attribute: (identifier))
                arguments: (argument_list)))
        """
        call = node.child(0)
        function = self.parse_identifier(
            call.child_by_field_name("function").child_by_field_name("attribute")
        )
        expr = call.child_by_field_name("arguments")
        expr = self.search(self.parse_expr, expr)
        expr = [self.parse_expr(arg) for arg in expr]

        match function.name:
            case "requires" if len(expr) == 1:
                return Requires(pos(node), expr[0])
            case _:
                raise ValueError(f"Unsupported object: {node.sexp()}")

    def parse_ensures_statement(self, node: TSNode) -> Ensures:
        """
        (expression_statement
            (call
                function: (attribute object: (identifier) attribute: (identifier))
                arguments: (argument_list)))
        """
        call = node.child(0)
        function = self.parse_identifier(
            call.child_by_field_name("function").child_by_field_name("attribute")
        )
        expr = call.child_by_field_name("arguments")
        expr = self.search(self.parse_expr, expr)
        expr = [self.parse_expr(arg) for arg in expr]

        match function.name:
            case "ensures" if len(expr) == 1:
                return Ensures(pos(node), expr[0])
            case _:
                raise ValueError(f"Unsupported object: {node.sexp()}")

    def parse_module(self, node: TSNode) -> DfyModule:
        """
        (decorated_definition
            (decorator (attribute object: (identifier) attribute: (identifier)))
            definition: (function_definition
                name: (identifier)
                parameters: (parameters)
                body: (block))
        )
        """

        assert self.text(node.children[0]) == "@dafnypy.verify"
        # TODO: this should actually probably be returning None
        function_def = node.children[1]

        name = self.parse_identifier(function_def.child_by_field_name("name"))
        params = function_def.child_by_field_name("parameters")
        body = function_def.child_by_field_name("body")
        pn = pos(node)

        parsed_params = self.parse_parameters(params)

        stmts = [self.parse_statement(child) for child in body.children]

        ensures = [s for s in stmts if isinstance(s, Ensures)]
        requires = [s for s in stmts if isinstance(s, Requires)]

        stmts = [
            s
            for s in stmts
            if not isinstance(s, Ensures) and not isinstance(s, Requires)
        ]

        parsed_body = s.Block(pos(body), [s for s in stmts if s is not None])
        return_type = self.parse_type(function_def.child_by_field_name("return_type"))

        return DfyModule(
            pn,
            "method",
            name,
            parsed_params,
            return_type,
            parsed_body,
            requires,
            ensures,
        )
