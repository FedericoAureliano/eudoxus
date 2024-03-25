import ast

from .utils import dump, generator_log

log = generator_log

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
    "Invert": "!",
    "In": "??",
    "Is": "??",
    "IsNot": "??",
    "NotIn": "??",
    "FloorDiv": "/",
    "MatMult": "??",
}

reserved = [
    "integer",
    "boolean",
    "real",
    "enum",
    "record",
    "instance",
    "type",
    "function",
    "invariant",
    "init",
    "next",
    "control",
    "input",
    "output",
    "sharedvar",
    "var",
]

INSTANCE_ARG_COMMENT = "Instance argument must be a local variable name, not an \
expression."

PRIMED_ASSIGN_COMMENT = "The lhs of an assignment in the next block must be primed."

INSTANCE_NOT_VAR_COMMENT = "To declare an instance you must use the 'instance' keyword."

RESERVED_WORD_COMMENT = "Cannot use a reserved word as a variable name."


class Stmt:
    pass


class AssignmentStmt(Stmt):
    """
    Assignment is a class that represents an assignment statement.
    """

    def __init__(self, lhs, rhs, primed=False):
        self.lhs = lhs
        self.rhs = rhs
        self.primed = primed

    __match_args__ = ("lhs", "rhs", "primed")

    def __str__(self, indent=0):
        space = "  " * indent
        prime = "'" if self.primed and "??" not in self.lhs else ""
        if self.primed and "??" in self.lhs:
            comment = CommentStmt(PRIMED_ASSIGN_COMMENT).__str__(indent)
            return f"{comment}\n{space}{self.lhs}{prime} = {self.rhs};"
        return f"{space}{self.lhs}{prime} = {self.rhs};"


class IfStmt(Stmt):
    """
    IfStmt is a class that represents an if statement.
    """

    def __init__(self, cond, true_stmt, false_stmt):
        self.cond = cond
        self.true_stmt = true_stmt
        self.false_stmt = false_stmt

    __match_args__ = ("cond", "true_stmt", "false_stmt")

    def __str__(self, indent=0):
        space = "  " * indent
        t = self.true_stmt.__str__(indent + 1)
        f = self.false_stmt.__str__(indent + 1)
        cond = str(self.cond)
        if cond.startswith("(") and cond.endswith(")"):
            cond = cond[1:-1]
        # check if both are empty
        if (f.isspace() or f == "") and (t.isspace() or t == ""):
            return ""
        # check if t has only whitespace
        elif f.isspace() or f == "":
            return f"{space}if ({cond}) {{\n{t}\n{space}}}"
        # check if f has only whitespace
        elif t.isspace() or t == "":
            return f"{space}if (!{self.cond}) {{\n{f}\n{space}}}"
        else:
            return f"{space}if ({cond}) {{\n{t}\n{space}}} else {{\n{f}\n{space}}}"


class ForStmt(Stmt):
    """
    ForStmt is a class that represents a for statement.
    """

    def __init__(self, var, range, body):
        self.var = var
        self.range = range
        self.body = body

    __match_args__ = ("var", "range", "body")

    def __str__(self, indent=0):
        space = "  " * indent
        b = self.body.__str__(indent + 1)
        if b.isspace() or b == "":
            return ""
        return f"{space}for {self.var} in {self.range} {{\n{b}\n{space}}}"


class NextStmt(Stmt):
    """
    NextStmt is a class that represents a next statement.
    """

    def __init__(self, instance):
        self.instance = instance

    def __str__(self, indent=0):
        space = "  " * indent
        return f"{space}next({self.instance});"


class AssumeStmt(Stmt):
    """
    AssumeStmt is a class that represents an assume statement.
    """

    def __init__(self, expr):
        self.expr = expr

    def __str__(self, indent=0):
        space = "  " * indent
        return f"{space}assume({self.expr});"


class AssertStmt(Stmt):
    """
    AssertStmt is a class that represents an assert statement.
    """

    def __init__(self, expr):
        self.expr = expr

    def __str__(self, indent=0):
        space = "  " * indent
        return f"{space}assert({self.expr});"


class HavocStmt(Stmt):
    """
    HavocStmt is a class that represents a havoc statement.
    """

    def __init__(self, var):
        self.var = var

    def __str__(self, indent=0):
        space = "  " * indent
        return f"{space}havoc({self.var});"


class BlockStmt(Stmt):
    """
    BlockStmt is a class that represents a block statement.
    """

    def __init__(self, stmts):
        self.stmts = stmts

    __match_args__ = ("stmts",)

    def __str__(self, indent=0):
        filtered = list(filter(lambda stmt: not isinstance(stmt, Skip), self.stmts))
        return "\n".join([stmt.__str__(indent) for stmt in filtered])


class CommentStmt(Stmt):
    """
    Comment is a class that represents a comment statement.
    """

    def __init__(self, comment):
        if not isinstance(comment, str):
            assert False, f"comment is not a string: {comment}"
        self.comment = comment

    def __str__(self, indent=0):
        space = "  " * indent
        # split the comment into lines and add // to each line
        lines = self.comment.split("\n")
        return "\n".join([f"{space}// {line}" for line in lines])


class HoleStmt(Stmt):
    """
    HoleStmt is a class that represents a hole statement.
    """

    def __init__(self):
        pass

    def __str__(self, indent=0):
        space = "  " * indent
        return f"{space}??;"


class Skip:
    pass


class Cmd:
    pass


class InductionCmd(Cmd):
    def __init__(self, k=1):
        self.k = k

    def __str__(self, indent=0):
        space = "  " * indent
        return f"{space}induction({self.k});\n{space}check;\n{space}print_results();"


class BoundedModelCheckingCmd(Cmd):
    def __init__(self, k=1):
        self.k = k

    def __str__(self, indent=0):
        space = "  " * indent
        return f"{space}bmc({self.k});\n{space}check;\n{space}print_results();"


class Decl:
    pass


class InstanceDecl(Decl):
    """
    Instance is a class that represents an instance of a module.
    """

    def __init__(self, name, module, kwargs=None):
        self.name = name
        self.module = module
        self.kwargs = kwargs if kwargs is not None else []

    def __str__(self, indent=0):
        space = "  " * indent
        m = self.module.name
        return f"{space}instance {self.name} : {m}({', '.join(self.kwargs)});"


class TyepDecl(Decl):
    """
    TypeDecl is a class that represents a type declaration.
    """

    def __init__(self, name, type, annonymous=False):
        self.name = name
        self.type = type
        self.annonymous = annonymous

    def __str__(self, indent=0):
        if self.annonymous:
            return ""
        space = "  " * indent
        return f"{space}type {self.name} = {self.type};"


class FuncDecl(Decl):
    """
    FuncDecl is a class that represents a function declaration.
    """

    def __init__(self, name, args):
        self.name = name
        self.args = args

    def __str__(self, indent=0):
        space = "  " * indent
        ret = self.args[-1]
        arg_types = self.args[:-1]
        arg_names = [f"x{i}" for i in range(len(arg_types))]
        args = list(map(lambda x: f"{x[0]} : {x[1]}", zip(arg_names, arg_types)))
        return f"{space}function {self.name}({', '.join(args)}) : {ret};"


class VarDecl(Decl):
    """
    VarDecl is a class that represents a variable declaration.
    """

    def __init__(self, name, type, kind):
        self.name = name
        self.type = type
        self.kind = kind

    def __str__(self, indent=0):
        space = "  " * indent
        return f"{space}{self.kind} {self.name} : {self.type};"


class TransitionDecl(Decl):
    """
    TransitionDecl is a class that represents an init, next, or control declaration.
    """

    def __init__(self, stmts, kind):
        self.stmts = stmts
        self.kind = kind

    def __str__(self, indent=0):
        space = "  " * indent
        inner = BlockStmt(self.stmts).__str__(indent + 1)
        if inner.isspace() or inner == "":
            return ""
        return f"{space}{self.kind} {{\n{inner}\n{space}}}\n"


class InvariantDecl(Decl):
    """
    InvariantDecl is a class that represents an invariant declaration.
    """

    def __init__(self, name, formula):
        self.name = name
        self.formula = formula

    def __str__(self, indent=0):
        space = "  " * indent
        return f"{space}invariant {self.name}: {self.formula};"


class Type:
    pass


class AlgebraicDataType(Type):
    """
    AlgebraicDataType is a class that represents an algebraic data type.
    """

    def __init__(self, name, constructors):
        self.name = name
        # a selector is a pair (name, type)
        # a constructor is a pair (name, list of selectors)
        # constructors is a list of constructors
        self.constructors = constructors

    __match_args__ = ("name", "constructors")


class ModuleType(Type):
    """
    ModuleType is a class that represents the type of a module.
    """

    def __init__(self, name, modules=None):
        self.name = name
        self.toplevel = []
        self.init = None
        self.next = None
        self.proof = None
        self.modules = [] if modules is None else modules

    def add_input(self, name, type):
        self.toplevel.append(VarDecl(name, type, "input"))

    def add_output(self, name, type):
        self.toplevel.append(VarDecl(name, type, "output"))

    def add_sharedvar(self, name, type):
        self.toplevel.append(VarDecl(name, type, "sharedvar"))

    def add_local(self, name, type):
        self.toplevel.append(VarDecl(name, type, "var"))

    def push_tmp(self, name, type):
        self.toplevel.append(VarDecl(name, type, "tmp"))

    def pop_tmp(self):
        # find the last tmp and remove it
        for i in range(len(self.toplevel) - 1, -1, -1):
            toplevel = self.toplevel[i]
            if isinstance(toplevel, VarDecl) and toplevel.kind == "tmp":
                self.toplevel.pop(i)
                return toplevel

    def add_type(self, name, type, annonymous=False):
        self.toplevel.append(TyepDecl(name, type, annonymous))

    def add_func(self, name, args):
        self.toplevel.append(FuncDecl(name, args))

    def add_spec(self, name, formula):
        self.toplevel.append(InvariantDecl(name, formula))

    def add_init_statement(self, statement):
        self.init.append(statement)

    def add_next_statement(self, statement):
        self.prime_statments(statement)
        self.next.append(statement)

    def prime_statments(self, stmt):
        match stmt:
            case AssignmentStmt(_, _, _):
                stmt.primed = True
            case IfStmt(_, true_stmt, false_stmt):
                self.prime_statments(true_stmt)
                self.prime_statments(false_stmt)
            case BlockStmt(stmts):
                for stmt in stmts:
                    self.prime_statments(stmt)
            case ForStmt(_, _, body):
                self.prime_statments(body)
            case _:
                pass

    def add_proof_statement(self, statement):
        self.proof.append(statement)

    def add_instance(self, instance):
        self.toplevel.append(instance)

    def get_inputs(self):
        return [
            decl
            for decl in self.toplevel
            if isinstance(decl, VarDecl) and decl.kind == "input"
        ]

    def get_outputs(self):
        return [
            decl
            for decl in self.toplevel
            if isinstance(decl, VarDecl) and decl.kind == "output"
        ]

    def get_sharedvars(self):
        return [
            decl
            for decl in self.toplevel
            if isinstance(decl, VarDecl) and decl.kind == "sharedvar"
        ]

    def get_locals(self):
        return [
            decl
            for decl in self.toplevel
            if isinstance(decl, VarDecl) and decl.kind == "var"
        ]

    def get_tmps(self):
        return [
            decl
            for decl in self.toplevel
            if isinstance(decl, VarDecl) and decl.kind == "tmp"
        ]

    def get_types(self):
        return [decl for decl in self.toplevel if isinstance(decl, TyepDecl)]

    def get_functions(self):
        return [decl for decl in self.toplevel if isinstance(decl, FuncDecl)]

    def get_specs(self):
        return [decl for decl in self.toplevel if isinstance(decl, InvariantDecl)]

    def get_instances(self):
        return [decl for decl in self.toplevel if isinstance(decl, InstanceDecl)]

    def get_signature(self):
        return (self.name, self.get_inputs(), self.get_outputs(), self.get_sharedvars())

    def get_vars(self):
        return (
            self.get_inputs()
            + self.get_outputs()
            + self.get_sharedvars()
            + self.get_locals()
            + self.get_tmps()
        )

    def get_var(self, name):
        for var in self.get_vars():
            if var.name == name:
                return var
        return None

    def is_var(self, name):
        return self.get_var(name) is not None

    def get_var_type(self, name):
        if not self.is_var(name):
            return None
        t = self.get_var(name).type
        if self.is_type(t):
            t = self.get_type(t).type
        return t

    def get_type(self, name):
        for type in self.get_types():
            if type.name == name:
                return type
        return None

    def is_type(self, name):
        return self.get_type(name) is not None

    def is_module(self, name):
        for module in self.modules:
            if module.name == name:
                return True
        return False

    def get_func(self, name):
        for func in self.get_functions():
            if func.name == name:
                return func
        return None

    def is_func(self, name):
        return self.get_func(name) is not None

    def get_constructor(self, name):
        for type in self.get_types():
            match type.type:
                case AlgebraicDataType(_, constructors):
                    for constructor in constructors:
                        if constructor[0] == name:
                            return constructor
        return None

    def is_constructor(self, name):
        return self.get_constructor(name) is not None

    def get_constructor_type(self, name):
        (name, selectors) = self.get_constructor(name)
        return list(map(lambda x: x[1], selectors))

    def get_selector(self, name):
        for type in self.get_types():
            match type:
                case AlgebraicDataType(_, constructors):
                    for constructor in constructors:
                        for selector in constructor[1]:
                            if selector[0] == name:
                                return selector
        return None

    def is_selector(self, name):
        return self.get_selector(name) is not None

    def get_selector_type(self, name):
        (name, type) = self.get_selector(name)
        return type

    def get_func_return_type(self, name):
        func = self.get_func(name)
        return func.args[-1]

    def parse_uclid5_module_decl(self, stmt):
        match stmt:
            case ast.Expr(ast.Constant(value, _)) if isinstance(value, str):
                self.add_comment(value)

            case ast.FunctionDef("types", _, body, _, _, _):
                for decl in body:
                    self.parse_type_decl(decl)

            case ast.FunctionDef("functions", _, body, _, _, _):
                for decl in body:
                    self.parse_func_decl(decl)

            case ast.FunctionDef("inputs", _, body, _, _, _):
                for decl in body:
                    self.parse_input_decl(decl)
            case ast.FunctionDef("locals", _, body, _, _, _):
                for decl in body:
                    self.parse_local_decl(decl)
            case ast.FunctionDef("outputs", _, body, _, _, _):
                for decl in body:
                    self.parse_output_decl(decl)
            case ast.FunctionDef(f, _, body, _, _, _) if f in [
                "shared_vars",
                "sharedvars",
            ]:
                for decl in body:
                    self.parse_sharedvar_decl(decl)

            case ast.FunctionDef("instances", _, body, _, _, _):
                for decl in body:
                    self.parse_instance_decl(decl)

            case ast.FunctionDef("init", _, body, _, _, _):
                if self.init is None:
                    self.toplevel.append(TransitionDecl([], "init"))
                    self.init = self.toplevel[-1].stmts
                for stmt in body:
                    self.parse_init_stmt(stmt)
                self.toplevel.append(Skip())
            case ast.FunctionDef("next", _, body, _, _, _):
                if self.next is None:
                    self.toplevel.append(TransitionDecl([], "next"))
                    self.next = self.toplevel[-1].stmts
                for stmt in body:
                    self.parse_next_stmt(stmt)
                self.toplevel.append(Skip())

            case ast.FunctionDef("specification", _, body, _, _, _):
                for inv in body:
                    self.parse_invariant(inv)

            case ast.FunctionDef("proof", _, body, _, _, _):
                if self.proof is None:
                    self.toplevel.append(TransitionDecl([], "control"))
                    self.proof = self.toplevel[-1].stmts
                for cmd in body:
                    self.parse_proof_cmd(cmd)
                self.toplevel.append(Skip())

    def parse_type_decl(self, type_decl):
        match type_decl:
            case ast.Assign([type_name], value, _):
                match type_name:
                    case ast.Name(name, _):
                        lhs = name
                    case ast.Attribute(ast.Name("self", _), attr, _):
                        lhs = attr
                    case _:
                        log(f"type_names[0] is ??: {dump(type_decl)}")
                        lhs = "??"
                rhs = self.parse_type(value, lhs)
                self.add_type(lhs, rhs)
            case ast.Expr(ast.Constant(value, _)) if isinstance(value, str):
                self.add_comment(value)
            case _:
                log(f"type_decl is ??: {dump(type_decl)}")
                return "??"

    def parse_func_decl(self, func_decl):
        match func_decl:
            case ast.Assign([func_name], value, _):
                match func_name:
                    case ast.Name(name, _):
                        lhs = name
                    case ast.Attribute(ast.Name("self", _), attr, _):
                        lhs = attr
                    case _:
                        log(f"func_names[0] is ??: {dump(func_decl)}")
                        lhs = "??"
                match value:
                    case ast.Call(ast.Name(f), args, kwargs) if f.lower().startswith(
                        "fun"
                    ):
                        args = list(map(self.parse_type, args))
                        kwargs = list(
                            map(lambda kwarg: self.parse_type(kwarg.value), kwargs)
                        )
                        args = args + kwargs
                        self.add_func(lhs, args)
                    case _:
                        log(f"func_decl is ??: {dump(func_decl)}")
                        return "??"
            case ast.Expr(ast.Constant(value, _)) if isinstance(value, str):
                self.add_comment(value)
            case _:
                log(f"func_decl is ??: {dump(func_decl)}")
                return "??"

    def add_comment(self, comment):
        if len(self.toplevel) == 0:
            self.toplevel.append(CommentStmt(comment))
            return

        last = self.toplevel[-1]
        if isinstance(last, TransitionDecl):
            last.stmts.append(CommentStmt(comment))
        else:
            self.toplevel.append(CommentStmt(comment))

    def parse_name(self, name_expr):
        match name_expr:
            case ast.Name(name, _):
                return name
            case ast.Attribute(ast.Name("self", _), attr, _):
                return attr
            case ast.Constant(value, _) if isinstance(value, str):
                return value
            case _:
                log(f"name_expr is ??: {dump(name_expr)}")
                return "??"

    def parse_range(self, range_expr):
        match range_expr:
            case ast.Call(ast.Name("range", _), [start, stop], _):
                start = int(self.parse_expr(start)[0])
                stop = int(self.parse_expr(stop)[0]) - 1
                return f"range({start}, {stop})"
            case ast.Call(ast.Name("range", _), [stop], _):
                stop = int(self.parse_expr(stop)[0]) - 1
                return f"range(0, {stop})"
            case _:
                log(f"range_expr is ??: {dump(range_expr)}")
                return "??"

    def parse_type(self, type_expr, to_assign=None):
        if to_assign is None:
            to_assign = ""
        match type_expr:
            case ast.Name(t, _):
                if t == "int":
                    return "integer"
                elif t == "bool":
                    return "boolean"
                elif self.is_type(t):
                    return t
                log(f"type_expr name is ??: {dump(type_expr)}")
                return "??"
            case ast.Call(ast.Name(t, _), args, kwargs):
                if t.lower() in ["integer", "int", "natural", "nat"]:
                    return "integer"
                elif t.lower() in ["boolean", "bool"]:
                    return "boolean"
                elif t.lower() in ["real"]:
                    return "real"
                elif t.lower() in ["array"] and len(args) == 2:
                    return f"[{self.parse_type(args[0])}]{self.parse_type(args[1])}"
                elif t.lower() in ["array"] and len(kwargs) == 2:
                    index = "??"
                    element = "??"
                    for k in kwargs:
                        if k.arg.lower() in ["index", "idx", "in"]:
                            index = self.parse_type(k.value)
                        elif k.arg.lower() in [
                            "element",
                            "elements",
                            "elem",
                            "out",
                            "value",
                        ]:
                            element = self.parse_type(k.value)
                    if index == "??":
                        log(f"index is ??: {dump(type_expr)}")
                    if element == "??":
                        log(f"element is ??: {dump(type_expr)}")
                    return f"[{index}]{element}"
                elif t.lower() in ["array"]:
                    return "[??]??"
                elif t.lower() in ["bv", "bitvec", "bitvector"]:
                    if len(args) == 1:
                        return f"bv{self.parse_expr(args[0])[0]}"
                    elif len(args) == 2:
                        match args[0]:
                            case ast.Constant(name, _) if isinstance(name, str):
                                return f"bv{self.parse_expr(args[1])[0]}"
                            case _:
                                log(f"bv args is len 2 and ??: {dump(type_expr)}")
                                return "bv??"
                    elif len(kwargs) == 1:
                        _, k = self.parse_expr(kwargs[0].value)
                        return f"bv{k}"
                    else:
                        log(f"bv args is ??: {dump(type_expr)}")
                        return "bv??"
                elif t.lower() in ["enum", "enumerated", "enumeration"]:
                    args = list(map(lambda x: self.parse_expr(x)[0], args))
                    if len(args) == 2 and " " in args[1]:
                        args = args[1].split(" ")
                        out = f"enum {{ {', '.join(args)} }}"
                    elif len(kwargs) > 0:
                        log(f"enum with kwargs is ??: {dump(type_expr)}")
                        out = "enum { ?? }"
                    else:
                        out = f"enum {{ {', '.join(args)} }}"
                    # add enum to types
                    adt = AlgebraicDataType(to_assign, [(c, []) for c in args])
                    log(f"adding enum to types: {to_assign}")
                    self.add_type(out, adt, annonymous=True)
                    return out
                elif t.lower() in ["rec", "record"]:
                    fields = []
                    if len(args) == 1 and isinstance(args[0], ast.Dict):
                        keys = args[0].keys
                        values = args[0].values
                        for k, v in zip(keys, values):
                            k = self.parse_name(k)
                            kwargs.append(ast.keyword(k, v))
                        args = []
                    for arg in args + kwargs:
                        match arg:
                            case ast.keyword(name, type_expr):
                                fields.append((name, self.parse_type(type_expr)))
                            case _:
                                log(f"record arg is ??: {dump(arg)}")
                                fields.append(("??", "??"))
                    args = list(map(lambda x: f"{x[0]} : {x[1]}", fields))
                    out = f"record {{ {', '.join(args)} }}"
                    # add record to types
                    adt = AlgebraicDataType(to_assign, [(to_assign, fields)])
                    log(f"adding record to types: {to_assign}")
                    self.add_type(out, adt, annonymous=True)
                    return out
                elif self.is_module(t):
                    log(f"type_expr call is instance ??: {dump(type_expr)}")
                    self.add_comment(INSTANCE_NOT_VAR_COMMENT)
                    return "??"
                elif self.is_type(t) and len(args + kwargs) == 0:
                    # we don't support type parameters yet (except for arrays)
                    return t
                else:
                    log(f"type_expr call is ??: {dump(type_expr)}")
                    return "??"
            case ast.Call(ast.Attribute(ast.Name("self", _), attr, ctx), args, kwargs):
                return self.parse_type(ast.Call(ast.Name(attr, ctx), args, kwargs))
            case _:
                name = self.parse_name(type_expr)
                if self.is_type(name):
                    return name
                log(f"type_expr is ??: {dump(type_expr)}")
                return "??"

    def parse_var_decl(self, var_decl, action):
        match var_decl:
            case ast.Assign([var_name], value, _):
                lhs = self.parse_name(var_name)
                if lhs in reserved:
                    self.is_constructor(RESERVED_WORD_COMMENT)
                    log(f"var_decl is reserved ??: {dump(var_decl)}")
                    lhs = "??"
                rhs = self.parse_type(value)
                action(lhs, rhs)
            case ast.Expr(ast.Constant(value, _)) if isinstance(value, str):
                self.add_comment(value)
            case _:
                log(f"var_decl is ??: {dump(var_decl)}")
                return "??"

    def parse_input_decl(self, decl):
        self.parse_var_decl(decl, self.add_input)

    def parse_local_decl(self, decl):
        self.parse_var_decl(decl, self.add_local)

    def parse_output_decl(self, decl):
        self.parse_var_decl(decl, self.add_output)

    def parse_sharedvar_decl(self, decl):
        self.parse_var_decl(decl, self.add_sharedvar)

    def parse_instance_decl(self, inst_decl):
        match inst_decl:
            case ast.Assign([inst_name], inst_expr, _):
                lhs = self.parse_name(inst_name)
                match inst_expr:
                    case ast.Call(func, _, keywords):
                        match func:
                            case ast.Name(name, _):
                                rhs = name
                            case _:
                                log(f"inst func is ??: {dump(inst_expr)}")
                                rhs = "??"
                        kwargs = []
                        for keyword in keywords:
                            match keyword:
                                case ast.keyword(arg, ast.Name(name, _)):
                                    # TODO: check arg
                                    if not self.is_var(name):
                                        name = "??"
                                    kwargs.append(f"{arg} : ({name})")
                                case ast.keyword(
                                    arg, ast.Attribute(ast.Name("self", _), name, _)
                                ):
                                    # TODO: check arg
                                    if not self.is_var(name):
                                        name = "??"
                                    kwargs.append(f"{arg} : ({name})")
                                case ast.keyword(arg, _):
                                    self.add_comment(INSTANCE_ARG_COMMENT)
                                    log(f"keyword expr is ??: {dump(keyword)}")
                                    kwargs.append(f"{arg} : (??)")
                                case _:
                                    log(f"keyword is ??: {dump(keyword)}")
                                    kwargs.append("??")
                        self.add_instance(InstanceDecl(lhs, ModuleType(rhs), kwargs))
                    case _:
                        log(f"inst_expr is ??: {dump(inst_decl)}")
                        return "??"
            case ast.Expr(ast.Constant(value, _)) if isinstance(value, str):
                self.add_comment(value)
            case _:
                log(f"inst_decl is ??: {dump(inst_decl)}")
                return "??"

    def parse_stmt(self, stmt):
        match stmt:
            case ast.Assign([ast.Tuple(lhss, _)], ast.Tuple(rhss, _), other) if len(
                lhss
            ) == len(rhss):
                assigns = [
                    ast.Assign([lhs], rhs, other) for (lhs, rhs) in zip(lhss, rhss)
                ]
                return BlockStmt(list(map(self.parse_stmt, assigns)))
            case ast.Assign([lhs_expr], value, _):
                # if the lhs is a subscript
                match lhs_expr:
                    case ast.Subscript(holder, position, _):
                        holder = self.parse_name(holder)
                        position, _ = self.parse_expr(position)
                        if not self.is_var(holder):
                            log(f"lhs is not var ??: {dump(stmt)}")
                            holder = "??"
                        rhs, _ = self.parse_expr(value)
                        return AssignmentStmt(holder, f"{holder}[{position} -> {rhs}]")
                # try to treat the lhs as a var
                lhs = self.parse_name(lhs_expr)
                if not self.is_var(lhs):
                    log(f"lhs is not var ??: {dump(stmt)}")
                    lhs = "??"
                    typ = None
                else:
                    typ = self.get_var_type(lhs)
                # otherwise, we may need to just havoc
                match value:
                    case ast.Call(ast.Name(f), args, kwargs):
                        if "rand" in f.lower():
                            return HavocStmt(lhs)
                        elif "any" in f.lower():
                            return HavocStmt(lhs)

                rhs, _ = self.parse_expr(value, typ)
                # if we are assigning to a type, then it is a havoc
                parsed_type = self.parse_type(value)
                if "??" in rhs and "??" not in parsed_type:
                    log(f"rhs is ?? type is not ?? ({parsed_type}): {dump(stmt)}")
                    return HavocStmt(lhs)

                return AssignmentStmt(lhs, rhs)
            case ast.AugAssign(lhs, op, rhs):
                lhs, typ1 = self.parse_expr(lhs)
                rhs, _ = self.parse_expr(rhs, typ1)
                return AssignmentStmt(
                    lhs, f"{lhs} {operator_dict[op.__class__.__name__]} {rhs}"
                )
            case ast.Expr(ast.Constant(value, _)) if isinstance(value, str):
                return CommentStmt(value)
            case ast.Expr(
                ast.Call(
                    ast.Attribute(
                        ast.Attribute(ast.Name("self", _), instance), "next", _
                    ),
                    _,
                    _,
                )
            ):
                return NextStmt(instance)
            case ast.Expr(ast.Call(ast.Name("assume"), args, kwargs)):
                if len(args) == 1:
                    k, _ = self.parse_expr(args[0])
                elif len(kwargs) == 1:
                    k, _ = self.parse_expr(kwargs[0].value)
                else:
                    k = "??"
                return AssumeStmt(k)
            case ast.Expr(ast.Call(ast.Name("havoc"), args, kwargs)):
                if len(args) == 1:
                    k, _ = self.parse_expr(args[0])
                elif len(kwargs) == 1:
                    k, _ = self.parse_expr(kwargs[0].value)
                else:
                    k = "??"
                return HavocStmt(k)
            case ast.Expr(ast.Call(ast.Name("assert"), args, kwargs)):
                if len(args) == 1:
                    k, _ = self.parse_expr(args[0])
                elif len(kwargs) == 1:
                    k, _ = self.parse_expr(kwargs[0].value)
                else:
                    k = "??"
                return AssertStmt(k)
            case ast.Expr(ast.Call(ast.Name(id), args, kwargs)) if id.lower() in [
                "if",
                "ite",
                "ifthenelse",
                "if_then_else",
                "ifelse",
                "if_else",
                "_if",
            ]:
                cond = self.parse_expr(args[0])[0]
                true_stmt = self.parse_stmt(args[1])
                false_stmt = self.parse_stmt(args[2])
                return IfStmt(cond, true_stmt, false_stmt)
            case ast.Assert(test, msg):
                if msg:
                    msg, _ = self.parse_expr(msg)
                    self.add_comment(msg)
                return AssertStmt(self.parse_expr(test)[0])
            case ast.If(test, body, orelse):
                return IfStmt(
                    self.parse_expr(test)[0],
                    BlockStmt(list(map(self.parse_stmt, body))),
                    BlockStmt(list(map(self.parse_stmt, orelse))),
                )
            case ast.With(_, body):
                log(f"stmt is if ??: {dump(stmt)}")
                return IfStmt(
                    "??",
                    BlockStmt(list(map(self.parse_stmt, body))),
                    BlockStmt([]),
                )
            case ast.For(target, iter, body, _):
                iter = self.parse_range(iter)
                target = self.parse_name(target)
                # push target onto locals
                self.push_tmp(target, "??")
                body = list(map(self.parse_stmt, body))
                self.pop_tmp()
                # pop target from locals
                return ForStmt(target, iter, BlockStmt(body))
            case ast.Pass():
                return Skip()
            case _:
                log(f"stmt is ??: {dump(stmt)}")
                return HoleStmt()

    def parse_init_stmt(self, stmt):
        self.add_init_statement(self.parse_stmt(stmt))

    def parse_next_stmt(self, stmt):
        self.add_next_statement(self.parse_stmt(stmt))

    def parse_invariant(self, inv):
        match inv:
            case ast.Return(value):
                if len(self.get_specs()) == 0:
                    name = "spec"
                else:
                    name = f"spec_{len(self.get_specs()) + 1}"
                self.add_spec(name, self.parse_expr(value, "boolean")[0])
            case ast.Expr(ast.Constant(value, _)) if isinstance(value, str):
                self.add_comment(value)
            case ast.Assert(test, msg):
                if msg:
                    msg, _ = self.parse_expr(msg)
                    self.add_comment(msg)
                if len(self.get_specs()) == 0:
                    name = "spec"
                else:
                    name = f"spec_{len(self.get_specs()) + 1}"
                self.add_spec(name, self.parse_expr(test, "boolean")[0])
            case _:
                log(f"inv is ??: {dump(inv)}")
                return "??"

    def parse_proof_cmd(self, cmd):
        match cmd:
            case ast.Expr(ast.Call(ast.Name(cmd), args, kwargs)):
                if len(args) == 1:
                    k, _ = self.parse_expr(args[0])
                elif len(kwargs) == 1:
                    k, _ = self.parse_expr(kwargs[0].value)
                else:
                    k = "??"

                if cmd.lower() in ["induction"]:
                    self.add_proof_statement(InductionCmd(k))
                elif cmd.lower() in ["bmc", "boundedmodelchecking", "unroll"]:
                    self.add_proof_statement(BoundedModelCheckingCmd(k))
            case ast.Expr(ast.Constant(value, _)) if isinstance(value, str):
                self.add_comment(value)
            case ast.Pass():
                return ""
            case _:
                log(f"cmd is ??: {dump(cmd)}")
                return "??"

    def parse_expr(self, expr, required_type=None):
        match expr:
            case ast.Name(name, _):
                if self.is_var(name):
                    return (name, self.get_var_type(name))
                elif self.is_constructor(name):
                    return (name, self.get_constructor_type(name))
                log(f"expr is name ??: {dump(expr)}")
                return ("??", None)
            case ast.Attribute(ast.Name("self", _), name, _):
                if self.is_var(name):
                    return (name, self.get_var_type(name))
                elif self.is_constructor(name):
                    return (name, self.get_constructor_type(name))
                log(f"expr attr is name ??: {dump(expr)}")
                return ("??", None)
            case ast.Attribute(value, attr, _):
                value, typ = self.parse_expr(value)
                return (f"{value}.{attr}", typ)
            case ast.Constant(value, _):
                if isinstance(value, bool):
                    out = "true" if value else "false"
                    return (out, "boolean")
                elif isinstance(value, int):
                    if isinstance(required_type, str) and required_type.startswith(
                        "bv"
                    ):
                        return (f"{value}{required_type}", required_type)
                    return (str(value), None)
                else:
                    return (str(value), None)
            case ast.Subscript(value, slice, _):
                value, _ = self.parse_expr(value)
                slice, _ = self.parse_expr(slice)
                return (f"{value}[{slice}]", None)
            case ast.IfExp(test, body, orelse):
                c, _ = self.parse_expr(test, "boolean")
                t, typ1 = self.parse_expr(body, required_type)
                f, typ2 = self.parse_expr(orelse, typ1)
                t, _ = self.parse_expr(body, typ2)
                return (f"if {c} then {t} else {f}", typ2)
            case ast.Compare(left, [op], [right]):
                op = operator_dict[op.__class__.__name__]
                _, typ1 = self.parse_expr(left)
                right, typ2 = self.parse_expr(right, typ1)
                left, _ = self.parse_expr(left, typ2)
                return (f"{left} {op} {right}", typ2)
            case ast.BinOp(left, op, right):
                op = operator_dict[op.__class__.__name__]
                _, typ1 = self.parse_expr(left, required_type)
                right, typ2 = self.parse_expr(right, typ1)
                left, _ = self.parse_expr(left, typ2)
                return (f"{left} {op} {right}", typ2)
            case ast.BoolOp(op, [x, y]):
                op = operator_dict[op.__class__.__name__]
                left, _ = self.parse_expr(x, "boolean")
                right, _ = self.parse_expr(y, "boolean")
                return (f"{left} {op} {right}", "boolean")
            case ast.BoolOp(op, [x]):
                op = operator_dict[op.__class__.__name__]
                only, _ = self.parse_expr(x, "boolean")
                return (f"{op}{only}", "boolean")
            case ast.UnaryOp(op, operand):
                op = operator_dict[op.__class__.__name__]
                only, typ1 = self.parse_expr(operand, required_type)
                return (f"{op}{only}", typ1)
            case ast.Call(func, args, kwargs):
                match func:
                    case ast.Name(name, _):
                        if name.lower().startswith("bv") or name.lower().startswith(
                            "bitvec"
                        ):
                            f = "bv"
                        else:
                            f = name
                    case ast.Attribute(ast.Name("self", _), name, _):
                        f = name
                    case ast.Call(
                        ast.Name(name, _), args_i, kwargs_i
                    ) if name.lower().startswith("bv") or name.lower().startswith(
                        "bitvec"
                    ):
                        log(f"expr func is bv: {dump(expr)}")
                        if len(args_i) == 1:
                            a, _ = self.parse_expr(args_i[0])
                            f = f"bv{a}"
                        elif len(kwargs_i) == 1:
                            k, _ = self.parse_expr(kwargs_i[0].value)
                            f = f"bv{k}"
                        else:
                            log(f"expr is bv ??: {dump(expr)}")
                            f = "bv??"
                    case _:
                        log(f"expr func is ??: {dump(func)}")
                        f = "??"

                if len(args) == 1 and isinstance(args[0], ast.Dict):
                    keys = args[0].keys
                    values = args[0].values
                    for k, v in zip(keys, values):
                        k = self.parse_name(k)
                        kwargs.append(ast.keyword(k, v))
                    args = []

                # TODO: make this typed and do type checking later. Right now we are
                # throwing away the type information
                args = list(map(lambda arg: self.parse_expr(arg)[0], args)) + list(
                    map(lambda kwarg: self.parse_expr(kwarg.value)[0], kwargs)
                )

                if f in operator_dict:
                    f = operator_dict[f]
                    if len(args) == 1:
                        return (f"{f}{args[0]}", None)
                    elif len(args) == 2:
                        return (f"({args[0]} {f} {args[1]})", None)
                    elif f in ["&&", "||"]:
                        f = " " + f + " "
                        return (f"({f.join(args)})", None)
                    else:
                        log(f"expr is op ??: {dump(expr)}")
                        return ("??", None)
                elif f.lower() in ["ite", "ifthenelse", "if", "if_"]:
                    if len(args) == 3:
                        return (f"if {args[0]} then {args[1]} else {args[2]}", None)
                    else:
                        log(f"expr is ite ??: {dump(expr)}")
                        return ("if ?? then ?? else ??", None)
                elif f.startswith("bv"):
                    if len(args) == 1 and f != "bv":
                        return (f"{args[0]}{f}", f)
                    elif len(args) == 2:
                        v = args[0] if args[0].isnumeric() else "??"
                        w = args[1] if args[1].isnumeric() else "??"
                        return (f"{v}bv{w}", f"bv{w}")
                    elif len(kwargs) == 1:
                        k, _ = self.parse_expr(kwargs[0].value)
                        return (f"{k}{f}", f)
                    elif len(kwargs) == 2:
                        w = "??"
                        v = "??"
                        for k in kwargs:
                            if k.arg.lower() in ["width", "size", "len"]:
                                w = self.parse_expr(k.value)
                            elif k.arg.lower() in ["value", "val", "v"]:
                                v = self.parse_expr(k.value)
                        if v == "??":
                            w = kwargs[0].value if kwargs[0].value.isnumeric() else "??"
                        if w == "??":
                            w = kwargs[1].value if kwargs[1].value.isnumeric() else "??"
                        return (f"{v}bv{w}", f"bv{w}")
                    else:
                        log(f"expr is bv ??: {dump(expr)}")
                        return ("??bv??", "bv??")
                elif self.is_constructor(f):
                    return (f"{f}({', '.join(args)})", self.get_constructor_type(f))
                elif self.is_selector(f):
                    return (
                        f"{self.parse_expr(args[0])}.{f}",
                        self.get_selector_type(f),
                    )
                elif self.is_func(f):
                    return (f"{f}({', '.join(args)})", self.get_func_return_type(f))
                else:
                    log(f"expr call {f} is ??: {dump(expr)}")
                    return ("??", None)
            case _:
                log(f"expr is ??: {expr} ({type(expr)})")
                return ("??", None)

    def __str__(self):
        return f"module {self.name} {{\n{BlockStmt(self.toplevel).__str__(1)}\n}}"


def compile_to_uclid5(python_ast, modules=None) -> str:
    """
    ast_to_ir converts a Python AST to the UCLID5 IR above and then prints.
    """
    if modules is None:
        modules = []
    match python_ast:
        case ast.Module(body):
            return "\n".join([compile_to_uclid5(stmt, modules) for stmt in body])
        case ast.ClassDef(name, _, _, body, _):
            mod = ModuleType(name, modules)
            modules.append(mod)
            for stmt in body:
                mod.parse_uclid5_module_decl(stmt)
            return mod.__str__()
        case _:
            log(f"python_ast is '': {dump(python_ast)}")
            return ""
