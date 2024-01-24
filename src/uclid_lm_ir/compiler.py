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
    "FloorDiv": "//",
    "MatMult": "??",
}

INSTANCE_ARG_COMMENT = (
    "Instance argument must be a local variable name, not an expression."
)


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
        prime = "'" if self.primed else ""
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
        # check if t has only whitespace
        if f.isspace() or f == "":
            return f"{space}if ({self.cond}) {{\n{t}\n{space}}}"
        # check if f has only whitespace
        elif t.isspace() or t == "":
            return f"{space}if (!{self.cond}) {{\n{f}\n{space}}}"
        else:
            return f"{space}if ({self.cond}) {{\n{t}\n{space}}} else {{\n{f}\n{space}}}"


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

    def __init__(self, vars):
        self.vars = vars

    def __str__(self, indent=0):
        space = "  " * indent
        return f"{space}havoc({', '.join(self.vars)});"


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
        self.comment = comment

    def __str__(self, indent=0):
        space = "  " * indent
        return f"{space}// {self.comment}"


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

    def __init__(self, name):
        self.name = name
        self.toplevel = []
        self.init = None
        self.next = None
        self.proof = None

    def add_input(self, name, type):
        self.toplevel.append(VarDecl(name, type, "input"))

    def add_output(self, name, type):
        self.toplevel.append(VarDecl(name, type, "output"))

    def add_sharedvar(self, name, type):
        self.toplevel.append(VarDecl(name, type, "sharedvar"))

    def add_local(self, name, type):
        self.toplevel.append(VarDecl(name, type, "var"))

    def add_type(self, name, type, annonymous=False):
        self.toplevel.append(TyepDecl(name, type, annonymous))

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

    def get_types(self):
        return [decl for decl in self.toplevel if isinstance(decl, TyepDecl)]

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
        )

    def get_var(self, name):
        for var in self.get_vars():
            if var.name == name:
                return var
        return None

    def is_var(self, name):
        return self.get_var(name) is not None

    def get_var_type(self, name):
        return self.get_var(name)[1] if self.is_var(name) else None

    def get_type(self, name):
        for type in self.get_types():
            if type.name == name:
                return type
        return None

    def is_type(self, name):
        return self.get_type(name) is not None

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

    def parse_uclid5_module_decl(self, stmt):
        match stmt:
            case ast.Expr(ast.Constant(value, _)) if isinstance(value, str):
                self.add_comment(value)

            case ast.FunctionDef("types", _, body, _, _, _):
                for decl in body:
                    self.parse_type_decl(decl)

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
            case ast.Assign(type_names, value, _):
                match type_names[0]:
                    case ast.Name(name, _):
                        lhs = name
                    case ast.Attribute(ast.Name("self", _), attr, _):
                        lhs = attr
                    case _:
                        log(f"type_names[0] is ??: {dump(type_decl)}")
                        lhs = "??"
                rhs = self.parse_type(value)
                self.add_type(lhs, rhs)
            case ast.Expr(ast.Constant(value, _)) if isinstance(value, str):
                self.add_comment(value)
            case _:
                log(f"type_decl is ??: {dump(type_decl)}")
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

    def parse_type(self, type_expr):
        match type_expr:
            case ast.Name(name, _):
                return name
            case ast.Attribute(ast.Name("self", _), attr, _):
                return attr
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
                elif t.lower() in ["bv", "bitvector"]:
                    if len(args) == 1:
                        return f"bv{self.parse_expr(args[0])}"
                    elif len(kwargs) == 1:
                        _, k = self.parse_expr(kwargs[0].value)
                        return f"bv{k}"
                    else:
                        log(f"bv args is ??: {dump(type_expr)}")
                        return "bv??"
                elif t.lower() in ["enum", "enumerated"]:
                    args = list(map(self.parse_expr, args))
                    if len(args) == 2 and " " in args[1]:
                        args = args[1].split(" ")
                        out = f"enum {{ {', '.join(args)} }}"
                    elif len(kwargs) > 0:
                        log(f"enum with kwargs is ??: {dump(type_expr)}")
                        out = "enum { ?? }"
                    else:
                        out = f"enum {{ {', '.join(args)} }}"
                    # add enum to types
                    adt = AlgebraicDataType(t, [(c, []) for c in args])
                    self.add_type(out, adt, annonymous=True)
                    return out
                elif self.is_type(t):
                    return t
                else:
                    log(f"type_expr is ??: {dump(type_expr)}")
                    return "??"
            case ast.Call(ast.Attribute(ast.Name("self", _), attr, ctx), args, kwargs):
                return self.parse_type(ast.Call(ast.Name(attr, ctx), args, kwargs))
            case _:
                log(f"type_expr is ??: {dump(type_expr)}")
                return "??"

    def parse_var_decl(self, var_decl, action):
        match var_decl:
            case ast.Assign(var_names, value, _):
                match var_names[0]:
                    case ast.Name(name, _):
                        lhs = name
                    case ast.Attribute(ast.Name("self", _), attr, _):
                        lhs = attr
                    case _:
                        log(f"var_names[0] is ??: {dump(var_decl)}")
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
            case ast.Assign(inst_names, inst_expr, _):
                match inst_names[0]:
                    case ast.Name(name, _):
                        lhs = name
                    case ast.Attribute(ast.Name("self", _), attr, _):
                        lhs = attr
                    case _:
                        log(f"inst_names[0] is ??: {dump(inst_decl)}")
                        lhs = "??"
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
            case ast.Assign(lhs_exprs, value, _):
                match lhs_exprs[0]:
                    case ast.Name(name, _):
                        lhs = name
                    case ast.Attribute(ast.Name("self", _), attr, _):
                        lhs = attr
                    case _:
                        log(f"lhs_exprs[0] is ??: {dump(stmt)}")
                        lhs = "??"
                if not self.is_var(lhs):
                    log(f"lhs is not var ??: {dump(stmt)}")
                    lhs = "??"
                rhs = self.parse_expr(value)
                return AssignmentStmt(lhs, rhs)
            case ast.AugAssign(lhs, op, rhs):
                lhs = self.parse_expr(lhs)
                rhs = self.parse_expr(rhs)
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
                    k = self.parse_expr(args[0])
                elif len(kwargs) == 1:
                    _, k = self.parse_expr(kwargs[0].value)
                else:
                    k = "??"
                return AssumeStmt(k)
            case ast.Expr(ast.Call(ast.Name("havoc"), args, kwargs)):
                if len(args) == 1:
                    k = self.parse_expr(args[0])
                elif len(kwargs) == 1:
                    _, k = self.parse_expr(kwargs[0].value)
                else:
                    k = "??"
                return HavocStmt(k)
            case ast.Expr(ast.Call(ast.Name("assert"), args, kwargs)):
                if len(args) == 1:
                    k = self.parse_expr(args[0])
                elif len(kwargs) == 1:
                    _, k = self.parse_expr(kwargs[0].value)
                else:
                    k = "??"
                return AssertStmt(k)
            case ast.Assert(test, msg):
                if msg:
                    self.add_comment(msg)
                return AssertStmt(self.parse_expr(test))
            case ast.If(test, body, orelse):
                return IfStmt(
                    self.parse_expr(test),
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
                self.add_spec(name, self.parse_expr(value))
            case ast.Expr(ast.Constant(value, _)) if isinstance(value, str):
                self.add_comment(value)
            case ast.Assert(test, msg):
                if msg:
                    self.add_comment(msg)
                if len(self.get_specs()) == 0:
                    name = "spec"
                else:
                    name = f"spec_{len(self.get_specs()) + 1}"
                self.add_spec(name, self.parse_expr(test))
            case _:
                log(f"inv is ??: {dump(inv)}")
                return "??"

    def parse_proof_cmd(self, cmd):
        match cmd:
            case ast.Expr(ast.Call(ast.Name(cmd), args, kwargs)):
                if len(args) == 1:
                    k = self.parse_expr(args[0])
                elif len(kwargs) == 1:
                    _, k = self.parse_expr(kwargs[0].value)
                else:
                    k = "??"

                if cmd.lower() in ["induction"]:
                    self.add_proof_statement(InductionCmd(k))
                elif cmd.lower() in ["bmc", "boundedmodelchecking", "unroll"]:
                    self.add_proof_statement(BoundedModelCheckingCmd(k))
            case ast.Expr(ast.Constant(value, _)) if isinstance(value, str):
                self.add_comment(value)
            case _:
                log(f"cmd is ??: {dump(cmd)}")
                return "??"

    def parse_expr(self, expr):
        match expr:
            case ast.Name(name, _):
                if self.is_var(name):
                    return name
                elif self.is_constructor(name):
                    return name
                log(f"expr is name ??: {dump(expr)}")
                return "??"
            case ast.Attribute(ast.Name("self", _), name, _):
                if self.is_var(name):
                    return name
                elif self.is_constructor(name):
                    return name
                log(f"expr attr is name ??: {dump(expr)}")
                return "??"
            case ast.Attribute(value, attr, _):
                return f"{self.parse_expr(value)}.{attr}"
            case ast.Constant(value, _):
                if isinstance(value, bool):
                    return "true" if value else "false"
                else:
                    return str(value)
            case ast.Subscript(value, slice, _):
                return f"{self.parse_expr(value)}[{self.parse_expr(slice)}]"
            case ast.IfExp(test, body, orelse):
                c = self.parse_expr(test)
                t = self.parse_expr(body)
                f = self.parse_expr(orelse)
                return f"if {c} then {t} else {f}"
            case ast.Compare(left, [op], [right]):
                op = operator_dict[op.__class__.__name__]
                return f"{self.parse_expr(left)} {op} {self.parse_expr(right)}"
            case ast.BinOp(left, op, right):
                op = operator_dict[op.__class__.__name__]
                return f"{self.parse_expr(left)} {op} {self.parse_expr(right)}"
            case ast.BoolOp(op, [x, y]):
                op = operator_dict[op.__class__.__name__]
                return f"{self.parse_expr(x)} {op} {self.parse_expr(y)}"
            case ast.BoolOp(op, [x]):
                return f"{operator_dict[op.__class__.__name__]}{self.parse_expr(x)}"
            case ast.UnaryOp(op, operand):
                return (
                    f"{operator_dict[op.__class__.__name__]}{self.parse_expr(operand)}"
                )
            case ast.Call(func, args, kwargs):
                match func:
                    case ast.Name(name, _):
                        f = name
                    case ast.Attribute(ast.Name("self", _), name, _):
                        f = name
                    case ast.Call(
                        ast.Name(name, _), args_i, kwargs_i
                    ) if name.lower() in ["bitvector", "bv"]:
                        if len(args_i) == 1:
                            a = self.parse_expr(args_i[0])
                            f = f"bv{a}"
                        elif len(kwargs_i) == 1:
                            _, k = self.parse_expr(kwargs_i[0].value)
                            f = f"bv{k}"
                        else:
                            log(f"expr is bv ??: {dump(expr)}")
                            f = "bv??"
                    case _:
                        log(f"expr func is ??: {dump(func)}")
                        f = "??"

                args = list(map(self.parse_expr, args)) + list(
                    map(lambda kwarg: self.parse_expr(kwarg.value), kwargs)
                )

                if f in operator_dict:
                    f = operator_dict[f]
                    if len(args) == 1:
                        return f"{f}{args[0]}"
                    elif len(args) == 2:
                        return f"{args[0]} {f} {args[1]}"
                    else:
                        log(f"expr is op ??: {dump(expr)}")
                        return "??"
                elif f.lower() in ["ite", "ifthenelse", "if", "if_"]:
                    if len(args) == 3:
                        return f"if {args[0]} then {args[1]} else {args[2]}"
                    else:
                        log(f"expr is ite ??: {dump(expr)}")
                        return "if ?? then ?? else ??"
                elif f.lower().startswith("bv"):
                    if len(args) == 1:
                        return f"{args[0]}{f}"
                    elif len(kwargs) == 1:
                        _, k = self.parse_expr(kwargs[0].value)
                        return f"{k}{f}"
                    else:
                        log(f"expr is bv ??: {dump(expr)}")
                        return "bv??"
                elif self.is_constructor(f):
                    return f"{f}({', '.join(args)})"
                elif self.is_selector(f):
                    return f"{self.parse_expr(args[0])}.{f}"
                else:
                    log(f"expr call {f} is ??: {dump(expr)}")
                    return "??"
            case _:
                log(f"expr is ??: {dump(expr)}")
                return "??"

    def __str__(self):
        return f"module {self.name} {{\n{BlockStmt(self.toplevel).__str__(1)}\n}}"


def compile_to_uclid5(python_ast) -> str:
    """
    ast_to_ir converts a Python AST to the UCLID5 IR above and then prints.
    """
    match python_ast:
        case ast.Module(body):
            return "\n".join([compile_to_uclid5(stmt) for stmt in body])
        case ast.ClassDef(name, _, _, body, _):
            mod = ModuleType(name)
            for stmt in body:
                mod.parse_uclid5_module_decl(stmt)
            return mod.__str__()
        case _:
            log(f"python_ast is ??: {dump(python_ast)}")
            return "??"
