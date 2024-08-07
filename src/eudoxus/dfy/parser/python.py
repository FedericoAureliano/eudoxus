from typing import List

from tree_sitter import Node as TSNode

import eudoxus.ast.expression as e
import eudoxus.ast.statement as s
from eudoxus.ast.node import Hole, Identifier, Position
from eudoxus.ast.type import Boolean, Float, Integer, Type
from eudoxus.dfy.ast import expression as dfy_e
from eudoxus.dfy.ast import statement as dfy_s
from eudoxus.dfy.ast.built_in import built_ins
from eudoxus.dfy.ast.list_and_sets import ListType
from eudoxus.dfy.ast.module import DfyModule
from eudoxus.dfy.ast.params import Param, Params
from eudoxus.dfy.ast.string import StringType
from eudoxus.parser.python import Parser, pos


class DfyParser(Parser):
    def __init__(self, src: str):
        super().__init__(src)
        self.ext_functions = set()
        self.variables = []

    def parse_identifier(self, node: TSNode, unique: bool = False) -> Identifier:
        """
        [
            {self.parse_flat_identifier.__doc__}
            {self.parse_self_identifier.__doc__}
        ]
        """

        match node.type:
            case "identifier":
                return self.parse_flat_identifier(node, unique=unique)
            case "attribute":
                return self.parse_self_identifier(node)

            case _:
                return Hole(pos(node))

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
        elif self.text(node) == "str":
            return StringType(pos(node))
        else:
            return Hole(pos(node))

    def parse_type(self, node: TSNode) -> Type:
        # case where it's a simple type

        if len(node.children) > 0 and node.children[0].type == "generic_type":
            match self.text(node.children[0].children[0]):
                case "List":
                    return ListType(
                        pos(node.children[0].children[0]),
                        self.parse_type(node.children[0].children[1].children[1]),
                    )
                case "Set":
                    return dfy_e.SetType(
                        pos(node),
                        self.parse_type(node.children[0].children[1].children[1]),
                    )
                case _:
                    return Hole(pos(node))

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

    def parse_app_expr(self, node: TSNode) -> e.Application:
        """
        (call
            function: {self.parse_identifier.__doc__}
            arguments: (argument_list))
        """

        def parse_args() -> List[e.Expression]:
            # If there's a "for_in_clause" we need to reject:
            if self._search("(for_in_clause)", node, strict=False):
                return [Hole(pos(node))]
            arguments = self.search(
                self.parse_expr, node.child_by_field_name("arguments")
            )
            arguments = [self.parse_expr(arg) for arg in arguments]
            return arguments

        fnode = node.child_by_field_name("function")
        function = self.parse_identifier(fnode)
        match function.name.lower():
            case "set" if parse_args() == []:
                return dfy_e.Set(pos(node), None)
            case "isinstance":
                return self.parse_isinstance(node)
            case _:
                arguments = parse_args()
                name = function.name
                if function.name == "set":
                    name = "cast_to_set"
                ret = self.expr_helper(pos(node), name, arguments)
                if isinstance(ret.callee, e.Identifier) and ret.callee.name != "len":
                    self.ext_functions.add(ret.callee.name)

                return ret

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
            case "expression_statement" if "append" in self.text(node):
                assert "append" == self.text(
                    node.child(0)
                    .child_by_field_name("function")
                    .child_by_field_name("attribute")
                )
                return self.parse_append(node)

            case "expression_statement":
                return self.parse_assignment(node)
            case "return_statement":
                return self.parse_return_statement(node)
            case "comment":
                return self.parse_comment(node)
            case "while_statement":
                return self.parse_while_statement(node)

            case _:
                print(f"Unsupported stmt: {node.sexp()}")
                return Hole(pos(node))

    def parse_isinstance(self, node: TSNode) -> dfy_e.IsInstance:
        function = node.child_by_field_name("function")
        assert self.text(function) == "isinstance"
        expr = node.child_by_field_name("arguments")
        filtered_expr = self.search(self.parse_expr, expr)
        if len(filtered_expr) < 2:
            obj, typ = Hole(pos(expr)), Hole(pos(expr))
        elif len(filtered_expr) == 2:
            obj, typ = self.parse_expr(filtered_expr[0]), self.parse_simple_type(
                filtered_expr[1]
            )

        else:
            print(f"Expected at most 1 argument, got {len(filtered_expr)}")
            obj, typ = Hole(pos(expr)), Hole(pos(expr))

        return dfy_e.IsInstance(pos(node), obj, typ)

    def parse_append(self, node: TSNode) -> s.Statement:
        call = node.child(0)
        lst = self.parse_identifier(
            call.child_by_field_name("function").child_by_field_name("object")
        )
        expr = call.child_by_field_name("arguments")
        filtered_expr = self.search(self.parse_expr, expr)
        parsed_expr = [self.parse_expr(arg) for arg in filtered_expr]
        if len(parsed_expr) == 0:
            elt = Hole(pos(expr))
        elif len(parsed_expr) == 1:
            elt = parsed_expr[0]
        else:
            raise ValueError(f"Expected at most 1 argument, got {len(parsed_expr)}")
        return dfy_s.Append(pos(node), lst, elt)

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
        left = node.child_by_field_name("left")

        lhs = self.parse_identifier(left)
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
        elif self.has_name(node.children[1], ":"):
            # typed
            return dfy_s.DeclAssignment(
                pos(node), lhs, rhs, self.parse_type(node.children[2])
            )

        else:
            print(f"Unsupported assignment: {node.sexp()}")
            return Hole(pos(node))

    def parse_empty_list(self, node: TSNode) -> e.Application:
        """
        (list)
        """
        return dfy_e.EmptyList(pos(node))

    def parse_flat_identifier(self, node: TSNode, unique: bool = False) -> Identifier:
        """(identifier)"""
        text = self.text(node)
        text_check = "".join([c for c in text if c.isalpha()])
        if text_check == "array":
            text = text.replace("array", "arr")
        if unique and text_check in list(built_ins.keys()) + ["power"]:
            text = text + "_method"
        # identifiers not allowed
        return Identifier(pos(node), text)

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
            {self.parse_empty_list.__doc__}
            {self.parse_forall_expression.__doc__}
            {self.parse_set_expression.__doc__}
            {self.parse_unary_expression.__doc__}
            (parenthesized_expression (_))
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
                    self.ext_functions.add(ret.callee.name)
                return ret
            case "call" if self.text(
                node.child_by_field_name("function")
            ) == "all" and node.child_by_field_name(
                "arguments"
            ).type == "generator_expression":
                return self.parse_forall_expression(node)
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
            case "subscript":
                return self.parse_subscript(node)
            case "conditional_expression":
                return self.parse_ite_expression(node)
            case "list":
                return self.parse_empty_list(node)
            case "set":
                return self.parse_set_expression(node)
            case "unary_operator":
                return self.parse_unary_expression(node)
            case "parenthesized_expression":
                return self.parse_expr(node.child(1))
            case _:
                print(f"Unsupported expr: {node.sexp()} of type {node.type}")
                return Hole(pos(node))

    def parse_unary_expression(self, node: TSNode) -> e.Application:
        """
        (unary_operator argument: (_))
        """
        if node.child(0).type == "-":
            return e.Application(
                pos(node),
                dfy_e.Neg(pos(node.child(0))),
                [self.parse_expr(node.child(1))],
            )
        else:
            return Hole(pos(node))

    def parse_set_expression(self, node: TSNode) -> dfy_e.Set:
        """
        (set (_))
        """
        # eventually going to need to support more than one element
        return dfy_e.Set(pos(node), [self.parse_expr(node.children[1])])

    def parse_subscript(self, node: TSNode) -> dfy_e.Subscript:
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
                        print(f"Too many slice entries: {self.text(subscript)}")

            parsed_subscript = dfy_e.Slice(pos(subscript), left, right, step)
        else:
            parsed_subscript = self.parse_expr(subscript)
        return dfy_e.Subscript(pos(node), list_value, parsed_subscript)

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

    def parse_ite_expression(self, node: TSNode) -> dfy_e.Ite:
        """
        (conditional_expression (_) (_) (_))
        """
        true_expr = self.parse_expr(node.child(0))
        condition = self.parse_expr(node.child(2))
        false_expr = self.parse_expr(node.child(4))

        return dfy_e.Ite(pos(node), condition, true_expr, false_expr)

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
        filtered_expr = self.search(self.parse_expr, expr)
        parsed_expr = [self.parse_expr(arg) for arg in filtered_expr]

        if function.name == ast_node.__name__.lower():
            if len(parsed_expr) == 1:
                return ast_node(pos(node), parsed_expr[0])
            else:
                print(f"Unsupported args: {node.sexp()} \n\n {self.text(node)}")
                return ast_node(pos(node), Hole(pos(node)))

        else:
            print(
                f"Unsupported reserved_function: {node.sexp()} \n\n {self.text(node)}"
            )
            return Hole(pos(node))

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
            case "in":
                return e.Application(p, dfy_e.In(p), args)
            case "not" if self.text(node.child(2)) == "in":
                return e.Application(p, e.Not(p), [e.Application(p, dfy_e.In(p), args)])
            case _:
                print(f"Unsupported object: {node.sexp()}")
                return Hole(p)

    def parse_forall_expression(self, node: TSNode) -> e.Application:
        """
        (call function: (identifier)
            arguments: (generator_expression)
        )
        """
        # all( predicate(x) for x in list if condition(x) )
        assert (
            self.text(node.child_by_field_name("function")) == "all"
        ), "Expected all function"
        predicate = self.parse_expr(
            node.child_by_field_name("arguments").child_by_field_name("body")
        )
        for_in_clause = self._search(
            "( for_in_clause )",
            node.child_by_field_name("arguments"),
            strict=False,
        )
        if not len(for_in_clause) == 1:
            print("Expected one for_in_clause")
            return Hole(pos(node))
        for_in_clause = for_in_clause[0]

        variable = self.parse_identifier(for_in_clause.child_by_field_name("left"))
        domain = self.parse_expr(for_in_clause.child_by_field_name("right"))
        # need to automatically handle if it's a range operator

        if_clause = self._search(
            "( if_clause )",
            node.child_by_field_name("arguments"),
            strict=False,
        )
        condition = None
        if len(if_clause) == 1:
            if_clause = if_clause[0]
            condition = self.parse_expr(if_clause.child(1))
            # predicate = e.Application (pos(node), e.Implies, [condition, predicate])
        elif len(if_clause) > 1:
            print(f"Expected one or none if_clause, got {len(if_clause)}")
            return Hole(pos(node))

        return dfy_e.ForAll(pos(node), variable, domain, predicate, condition)

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

        # assert self.text(node.children[0]) == "@dafnypy.verify"
        # TODO: this should actually probably be returning None
        function_def = node.children[1]

        name = self.parse_identifier(
            function_def.child_by_field_name("name"), unique=True
        )
        params = function_def.child_by_field_name("parameters")
        body = function_def.child_by_field_name("body")
        pn = pos(node)

        parsed_params = self.parse_parameters(params)

        stmts = [self.parse_statement(child) for child in body.children]

        rewritten_stmts = []
        for stmt in stmts:
            if isinstance(stmt, s.If):
                then_branch_stmts = []
                for entry in stmt.then_branch.statements:
                    if isinstance(entry, dfy_s.Ensures):
                        rewritten_stmts.append(
                            dfy_s.Ensures(
                                entry.position,
                                e.Application(
                                    entry.position,
                                    e.Implies(stmt.condition.position),
                                    [stmt.condition, entry.condition],
                                ),
                            )
                        )
                    else:
                        then_branch_stmts.append(entry)
                else_branch_stmts = []
                for entry in stmt.else_branch.statements:
                    if isinstance(entry, dfy_s.Ensures):
                        rewritten_stmts.append(
                            dfy_s.Ensures(
                                entry.position,
                                e.Application(
                                    entry.position,
                                    e.Implies(stmt.condition.position),
                                    [
                                        e.Application(
                                            stmt.condition.position,
                                            e.Not(stmt.condition.position),
                                            [stmt.condition],
                                        ),
                                        entry.condition,
                                    ],
                                ),
                            )
                        )
                    else:
                        else_branch_stmts.append(entry)
                then_empty = all(
                    isinstance(stmt, dfy_s.Comment) for stmt in then_branch_stmts
                )
                else_empty = all(
                    isinstance(stmt, dfy_s.Comment) for stmt in else_branch_stmts
                )
                if then_empty and else_empty:
                    for stmt in then_branch_stmts + else_branch_stmts:
                        rewritten_stmts.append(stmt)
                elif else_empty and not then_empty:
                    rewritten_stmts.append(
                        s.If(
                            stmt.position,
                            stmt.condition,
                            s.Block(stmt.then_branch.position, then_branch_stmts),
                            s.Block(stmt.else_branch.position, []),
                        )
                    )
                elif then_empty and not else_empty:
                    p = stmt.condition.position
                    rewritten_stmts.append(
                        s.If(
                            stmt.position,
                            e.Application(p, e.Not(p), [stmt.condition]),
                            s.Block(stmt.else_branch.position, else_branch_stmts),
                            s.Block(stmt.then_branch.position, []),
                        )
                    )

            else:
                rewritten_stmts.append(stmt)

        stmts = rewritten_stmts

        ensures = [s for s in stmts if isinstance(s, dfy_s.Ensures)]
        requires = [s for s in stmts if isinstance(s, dfy_s.Requires)]
        # decreases = [s for s in stmts if isinstance(s, dfy_s.Decreases)]

        stmts = [
            s
            for s in stmts
            if not isinstance(s, dfy_s.Ensures) and not isinstance(s, dfy_s.Requires)
            # and not isinstance(s, dfy_s.Decreases)
        ]

        # support case where result isn't the output name
        # return_stmts = [s for s in stmts if isinstance(s, dfy_s.Return)]

        def convert_to_assign(assign, ret_name):
            if assign.target.name != ret_name.name:
                return assign
            return s.Assignment(assign.position, assign.target, assign.value)

        return_type = self.parse_type(function_def.child_by_field_name("return_type"))

        if len([s for s in stmts if not isinstance(s, dfy_s.Comment)]) == 1:
            single_stmt = [s for s in stmts if not isinstance(s, dfy_s.Comment)][0]
            if isinstance(single_stmt, dfy_s.Return):
                # case where we have a function
                return DfyModule(
                    pn,
                    "function",
                    name,
                    parsed_params,
                    return_type,
                    None,
                    single_stmt.expr,
                    requires,
                    ensures,
                    [],  # decreases,
                )
        # only need to parse the return name if it's a method
        # if len(return_stmts) == 1:
        #     ret_name = return_stmts[0].expr.callee
        # else:
        ret_name = Identifier(None, "result")
        self.variables.append(ret_name.name)

        stmts = [
            stmt
            if not isinstance(stmt, dfy_s.DeclAssignment)
            else convert_to_assign(stmt, ret_name)
            for stmt in stmts
        ]
        parsed_body = s.Block(pos(body), [s for s in stmts if s is not None])

        return DfyModule(
            pn,
            "method",
            name,
            parsed_params,
            return_type,
            ret_name,
            parsed_body,
            requires,
            ensures,
            [],  # decreases,
        )

    def parse(self, builtins=True):
        modules = super().parse()
        if builtins:
            ext_fns = [
                built_in_module
                for built_in_name, built_in_module in built_ins.items()
                if any([built_in_name in ext_fn for ext_fn in self.ext_functions])
            ]

        else:
            ext_fns = []
        return ext_fns + modules

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
            case "**":
                self.ext_functions.add("power")
                return e.Application(p, dfy_e.Power(p), [left, right])
            case "%":
                return e.Application(p, e.Modulo(p), [left, right])
            case "//":
                return e.Application(p, dfy_e.IntDivide(p), [left, right])
            case _:
                print(
                    f"Unsupported binary expr: {node.sexp()}, "
                    + f"{self.text(node.child_by_field_name('operator'))}"
                )
                return Hole(p)
