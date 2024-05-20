from eudoxus.ast.expression import Application, GreaterThanOrEqual, Integer
from eudoxus.ast.node import Identifier, Position
from eudoxus.ast.type import Integer as IntegerType
from eudoxus.dfy.ast.expression import Ite, Neg
from eudoxus.dfy.ast.module import DfyModule
from eudoxus.dfy.ast.params import Param, Params


def offset(x: int) -> int:
    return x - 3000


abs_src = """import dafnypy

@dafnypy.verify
def abs(x: int) -> int:
    return x if x >= 0 else -x
"""
AbsModule = DfyModule(
    position=Position(unique=offset(16)),
    method_or_function="function",
    name=Identifier(position=Position(unique=offset(36)), name="abs"),
    params=Params(
        position=Position(unique=offset(39)),
        params=[
            Param(
                position=Position(unique=offset(40)),
                type=IntegerType(position=Position(unique=offset(43))),
                name=Identifier(position=Position(unique=offset(40)), name="x"),
            )
        ],
    ),
    return_type=IntegerType(position=Position(unique=offset(51))),
    ret_name=None,
    body=Ite(
        position=Position(unique=offset(67)),
        condition=Application(
            position=Position(unique=offset(72)),
            callee=GreaterThanOrEqual(position=Position(unique=offset(72))),
            arguments=[
                Application(
                    position=Position(unique=offset(72)),
                    callee=Identifier(position=Position(unique=offset(72)), name="x"),
                    arguments=[],
                ),
                Integer(position=Position(unique=offset(77)), value=0),
            ],
        ),
        then_expr=Application(
            position=Position(unique=offset(67)),
            callee=Identifier(position=Position(unique=offset(67)), name="x"),
            arguments=[],
        ),
        else_expr=Application(
            position=Position(unique=offset(84)),
            callee=Neg(position=Position(unique=offset(84))),
            arguments=[
                Application(
                    position=Position(unique=offset(85)),
                    callee=Identifier(position=Position(unique=offset(85)), name="x"),
                    arguments=[],
                )
            ],
        ),
    ),
    requires=[],
    ensures=[],
    decreases=[],
)
