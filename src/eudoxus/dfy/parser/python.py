from typing import List

from tree_sitter import Node as TSNode

import eudoxus.ast.expression as e
import eudoxus.ast.statement as s
from eudoxus.ast.node import Hole, Identifier, Position
from eudoxus.ast.type import Boolean, Float, Integer, Type
from eudoxus.dfy.ast import statement as dfy_s
from eudoxus.dfy.ast.built_in import built_ins
from eudoxus.dfy.ast.expression import Ite, Slice, Subscript
from eudoxus.dfy.ast.list import List as ListType
from eudoxus.dfy.ast.module import DfyModule
from eudoxus.dfy.ast.params import Param, Params
from eudoxus.parser.python import Parser, pos


class DfyParser(Parser):
    def __init__(self, src: str):
        super().__init__(src)
        self.ext_functions = []
        self.variables = []

    def parse_simple_type(self, node: TSNode) -> Type:
        """
        (type (identifier))
        """
        if self.text(node) == "int":
            return Integer(pos(node))
        elif self.text(node) == "bool":
            return Boolean(pos(node))
        elif self.text(node) == "float":
            return Float(pos(node))
        else:
            raise NotImplementedError

    def parse_type(self, node: TSNode) -> Type:
        # case where it's a simple type

        if node.children[0].type == "generic_type":
            match self.text(node.children[0].children[0]):
                case "List":
                    return ListType(
                        pos(node.children[0].children[0]),
                        self.parse_type(node.children[0].children[1].children[1]),
                    )
                case _:
                    raise NotImplementedError

        return self.parse_simple_type(node.children[0])

    def has_name(self, node: TSNode, name: str) -> bool:
        return node.type == name

    def parse_typed_parameter(self, node: TSNode, typed=True) -> Param:
        """
        (typed_parameter (identifier) type: (type (_)))
        """

        name = self.parse_identifier(node.children[0])
        self.variables.append(name.name)
        type = self.parse_type(node.child_by_field_name("type"))
        return Param(pos(node), type, name)

    def parse_untyped_parameter(self, node: TSNode) -> Param:
        """(identifier)"""
        self.variables.append(self.text(node))
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
            {self.parse_invariant_statement.__doc__}
            {self.parse_return_statement.__doc__}
            {self.parse_comment.__doc__}
            {self.parse_while_statement.__doc__}
            {self.parse_decreases_statement.__doc__}
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
                "dafnypy.invariant",
                "dafnypy.decreases",
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
                    case "dafnypy.invariant":
                        return self.parse_invariant_statement(node)
                    case "dafnypy.decreases":
                        return self.parse_decreases_statement(node)
                    case "havoc":
                        return self.parse_havoc_statement(node)
            case "expression_statement":
                return self.parse_assignment(node)
            case "return_statement":
                return self.parse_return_statement(node)
            case "comment":
                return self.parse_comment(node)
            case "while_statement":
                return self.parse_while_statement(node)

            case _:
                raise ValueError(f"Unsupported object: {node.sexp()}")

    def parse_assignment(self, node: TSNode) -> s.Assignment:
        """
        (expression_statement
            (assignment
                left: {self.parse_identifier.__doc__}
                right: {self.parse_expr.__doc__}))
        (expression_statement
                (augmented_assignment
                    left: {self.parse_identifier.__doc__}
                    right: {self.parse_expr.__doc__}))
        """

        node = node.child(0)
        lhs = self.parse_identifier(node.child_by_field_name("left"))
        decl = lhs.name not in self.variables and lhs.name != "result"
        if decl:
            self.variables.append(lhs.name)

        def get_assign(pos, lhs, rhs, decl=False):
            if decl:
                return dfy_s.DeclAssignment(
                    pos, lhs, rhs, Hole(Position(node.end_byte))
                )
            else:
                return s.Assignment(pos, lhs, rhs)

        p_rhs = pos(node.child_by_field_name("right"))
        rhs = self.parse_expr(node.child_by_field_name("right"))
        lhs_as_app = e.Application(p_rhs, lhs, [])
        if self.has_name(node.children[1], "="):
            return get_assign(pos(node), lhs, rhs, decl=decl)
        elif self.has_name(node.children[1], "+="):
            return get_assign(
                pos(node),
                lhs,
                e.Application(p_rhs, e.Add(p_rhs), [lhs_as_app, rhs]),
                decl=decl,
            )
        elif self.has_name(node.children[1], "-="):
            return get_assign(
                pos(node),
                lhs,
                e.Application(p_rhs, e.Add(p_rhs), [lhs_as_app, rhs]),
                decl=decl,
            )
        elif self.has_name(node.children[1], "*="):
            return get_assign(
                pos(node),
                lhs,
                e.Application(p_rhs, e.Add(p_rhs), [lhs_as_app, rhs]),
                decl=decl,
            )
        elif self.has_name(node.children[1], "/="):
            return get_assign(
                pos(node),
                lhs,
                e.Application(p_rhs, e.Add(p_rhs), [lhs_as_app, rhs]),
                decl=decl,
            )
        else:
            raise ValueError(f"Unsupported object: {node.sexp()}")

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
            {self.parse_subscript.__doc__}
            {self.parse_ite_expression.__doc__}
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
                ret = self.parse_app_of_app_expr(node)
                if isinstance(ret.callee, e.Identifier) and ret.callee.name != "len":
                    self.ext_functions.append(ret.callee.name)
                return ret
            case "call":
                ret = self.parse_app_expr(node)
                if isinstance(ret.callee, e.Identifier) and ret.callee.name != "len":
                    self.ext_functions.append(ret.callee.name)
                return ret
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
            case "subscript":
                return self.parse_subscript(node)
            case "conditional_expression":
                return self.parse_ite_expression(node)
            case _:
                raise ValueError(
                    f"Unsupported object: {node.sexp()} of type {node.type}"
                )

    def parse_subscript(self, node: TSNode) -> Subscript:
        """(subscript
            value: (_)
            subscript: (_)
        )"""
        list_value = self.parse_expr(node.child_by_field_name("value"))
        subscript = node.child_by_field_name("subscript")
        if subscript.type == "slice":
            slice_entries = [
                child if child.type != ":" else ":" for child in subscript.children
            ]

            position_in_slice = 0
            for slice_entry in slice_entries:
                if slice_entry == ":":
                    position_in_slice += 1
                else:
                    left, right, step = None, None, None
                    if position_in_slice == 0:
                        left = self.parse_expr(slice_entry)
                    elif position_in_slice == 1:
                        right = self.parse_expr(slice_entry)
                    elif position_in_slice == 2:
                        step = self.parse_expr(slice_entry)
                    else:
                        raise ValueError(
                            f"Too many slice entries: {self.text(subscript)}"
                        )

            parsed_subscript = Slice(pos(subscript), left, right, step)
        else:
            parsed_subscript = self.parse_expr(subscript)
        return Subscript(pos(node), list_value, parsed_subscript)

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
            case "add" | "plus" | "addition":
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

    def parse_ite_expression(self, node: TSNode) -> Ite:
        """
        (conditional_expression (_) (_) (_))
        """
        true_expr = self.parse_expr(node.child(0))
        condition = self.parse_expr(node.child(2))
        false_expr = self.parse_expr(node.child(4))
        return Ite(pos(node), condition, true_expr, false_expr)

    def parse_while_statement(self, node: TSNode) -> s.Statement:
        """
        (while_statement
            condition: (expression)
            body: (block))
        """
        cond = self._search(
            "(comparison_operator (_) (_) )",
            node.child_by_field_name("condition"),
            strict=False,
        )
        if len(cond) != 1:
            raise ValueError(
                f"Expected one condition, got {len(cond)},\n {node.sexp()}"
            )
        condition = self.parse_expr(cond[0])
        block_pos = pos(node.child_by_field_name("body"))
        stmts = [
            self.parse_statement(child)
            for child in node.child_by_field_name("body").children
        ]

        stmts = list(filter(lambda x: x is not None, stmts))

        invariant = [s for s in stmts if isinstance(s, dfy_s.Invariant)]
        decreases = [s for s in stmts if isinstance(s, dfy_s.Decreases)]
        body = s.Block(
            block_pos,
            [
                s
                for s in stmts
                if not isinstance(s, dfy_s.Invariant)
                and not isinstance(s, dfy_s.Decreases)
            ],
        )
        return dfy_s.While(pos(node), condition, invariant, decreases, body)

    def parse_return_statement(self, node: TSNode) -> dfy_s.Return:
        """
        (return_statement (_))
        """
        return dfy_s.Return(pos(node), self.parse_expr(node.children[1]))

    def parse_comment(self, node: TSNode) -> None:
        """
        (comment)
        """
        return dfy_s.Comment(pos(node), self.text(node))

    def parse_reserved_function(
        self, node: TSNode, ast_node: s.Statement
    ) -> s.Statement:
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

        if function.name == ast_node.__name__.lower() and len(expr) == 1:
            return ast_node(pos(node), expr[0])
        else:
            raise ValueError(f"Unsupported object: {node.sexp()}")

    def parse_requires_statement(self, node: TSNode) -> dfy_s.Requires:
        """
        (expression_statement
            (call
                function: (attribute object: (identifier) attribute: (identifier))
                arguments: (argument_list)))
        """
        return self.parse_reserved_function(node, dfy_s.Requires)

    def parse_ensures_statement(self, node: TSNode) -> dfy_s.Ensures:
        """
        (expression_statement
            (call
                function: (attribute object: (identifier) attribute: (identifier))
                arguments: (argument_list)))
        """
        return self.parse_reserved_function(node, dfy_s.Ensures)

    def parse_invariant_statement(self, node: TSNode) -> dfy_s.Invariant:
        """
        (expression_statement
            (call
                function: (attribute object: (identifier) attribute: (identifier))
                arguments: (argument_list)))
        """
        return self.parse_reserved_function(node, dfy_s.Invariant)

    def parse_decreases_statement(self, node: TSNode) -> dfy_s.Decreases:
        """
        (expression_statement
            (call
                function: (attribute object: (identifier) attribute: (identifier))
                arguments: (argument_list)))
        """
        return self.parse_reserved_function(node, dfy_s.Decreases)

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

        ensures = [s for s in stmts if isinstance(s, dfy_s.Ensures)]
        requires = [s for s in stmts if isinstance(s, dfy_s.Requires)]

        stmts = [
            s
            for s in stmts
            if not isinstance(s, dfy_s.Ensures) and not isinstance(s, dfy_s.Requires)
        ]

        # support case where result isn't the output name
        return_stmts = [s for s in stmts if isinstance(s, dfy_s.Return)]
        if len(return_stmts) == 1:
            ret_name = return_stmts[0].expr.callee
        else:
            ret_name = Identifier(None, "result")
        self.variables.append(ret_name.name)

        def convert_to_assign(assign, ret_name):
            if assign.target.name != ret_name.name:
                return assign
            return s.Assignment(assign.position, assign.target, assign.value)

        stmts = [
            stmt
            if not isinstance(stmt, dfy_s.DeclAssignment)
            else convert_to_assign(stmt, ret_name)
            for stmt in stmts
        ]

        parsed_body = s.Block(pos(body), [s for s in stmts if s is not None])
        return_type = self.parse_type(function_def.child_by_field_name("return_type"))

        if len([s for s in stmts if not isinstance(s, dfy_s.Comment)]) == 1:
            single_stmt = [s for s in stmts if not isinstance(s, dfy_s.Comment)][0]
            if isinstance(single_stmt, dfy_s.Return):
                return (
                    DfyModule(
                        pn,
                        "function",
                        name,
                        parsed_params,
                        return_type,
                        None,
                        single_stmt.expr,
                        requires,
                        ensures,
                    ),
                    self.ext_functions,
                )

        return (
            DfyModule(
                pn,
                "method",
                name,
                parsed_params,
                return_type,
                ret_name,
                parsed_body,
                requires,
                ensures,
            ),
            self.ext_functions,
        )

    def parse(self):
        modules = super().parse()
        only_modules = [m for m, _ in modules]
        ext_fns = [
            built_in_module
            for built_in_name, built_in_module in built_ins.items()
            if any([built_in_name in ext_fn for _, ext_fn in modules])
        ]
        return ext_fns + only_modules
