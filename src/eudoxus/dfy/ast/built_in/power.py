from eudoxus.ast.expression import (
    Application,
    Equal,
    GreaterThanOrEqual,
    Integer,
    Multiply,
    Subtract,
)
from eudoxus.ast.node import Identifier, Position
from eudoxus.ast.type import Integer as IntegerType
from eudoxus.dfy.ast.expression import Ite
from eudoxus.dfy.ast.module import DfyModule
from eudoxus.dfy.ast.params import Param, Params
from eudoxus.dfy.ast.statement import Decreases


def offset(x: int) -> int:
    return x - 4000


power_src = """import dafnypy

@dafnypy.verify
def power(x: int, pow: int) -> int:
    dafnypy.decreases(pow)
    return 1 if pow == 0 else (power(x, pow - 1) * x if pow >= 1 else 0)"""

PowerModule = DfyModule(
    position=Position(unique=offset(16)),
    method_or_function="function",
    name=Identifier(position=Position(unique=offset(36)), name="power"),
    params=Params(
        position=Position(unique=offset(41)),
        params=[
            Param(
                position=Position(unique=offset(42)),
                type=IntegerType(position=Position(unique=offset(45))),
                name=Identifier(position=Position(unique=offset(42)), name="x"),
            ),
            Param(
                position=Position(unique=offset(50)),
                type=IntegerType(position=Position(unique=offset(55))),
                name=Identifier(position=Position(unique=offset(50)), name="pow"),
            ),
        ],
    ),
    return_type=IntegerType(position=Position(unique=offset(63))),
    ret_name=None,
    body=Ite(
        position=Position(unique=offset(106)),
        condition=Application(
            position=Position(unique=offset(111)),
            callee=Equal(position=Position(unique=offset(111))),
            arguments=[
                Application(
                    position=Position(unique=offset(111)),
                    callee=Identifier(
                        position=Position(unique=offset(111)), name="pow"
                    ),
                    arguments=[],
                ),
                Integer(position=Position(unique=offset(118)), value=0),
            ],
        ),
        then_expr=Integer(position=Position(unique=offset(106)), value=1),
        else_expr=Ite(
            position=Position(unique=offset(126)),
            condition=Application(
                position=Position(unique=offset(151)),
                callee=GreaterThanOrEqual(position=Position(unique=offset(151))),
                arguments=[
                    Application(
                        position=Position(unique=offset(151)),
                        callee=Identifier(
                            position=Position(unique=offset(151)), name="pow"
                        ),
                        arguments=[],
                    ),
                    Integer(position=Position(unique=offset(158)), value=1),
                ],
            ),
            then_expr=Application(
                position=Position(unique=offset(126)),
                callee=Multiply(position=Position(unique=offset(126))),
                arguments=[
                    Application(
                        position=Position(unique=offset(126)),
                        callee=Identifier(
                            position=Position(unique=offset(126)), name="power"
                        ),
                        arguments=[
                            Application(
                                position=Position(unique=offset(132)),
                                callee=Identifier(
                                    position=Position(unique=offset(132)), name="x"
                                ),
                                arguments=[],
                            ),
                            Application(
                                position=Position(unique=offset(135)),
                                callee=Subtract(position=Position(unique=offset(135))),
                                arguments=[
                                    Application(
                                        position=Position(unique=offset(135)),
                                        callee=Identifier(
                                            position=Position(unique=offset(135)),
                                            name="pow",
                                        ),
                                        arguments=[],
                                    ),
                                    Integer(
                                        position=Position(unique=offset(141)), value=1
                                    ),
                                ],
                            ),
                        ],
                    ),
                    Application(
                        position=Position(unique=offset(146)),
                        callee=Identifier(
                            position=Position(unique=offset(146)), name="x"
                        ),
                        arguments=[],
                    ),
                ],
            ),
            else_expr=Integer(position=Position(unique=offset(165)), value=0),
        ),
    ),
    requires=[],
    ensures=[],
    decreases=[
        Decreases(
            position=Position(unique=offset(72)),
            condition=Application(
                position=Position(unique=offset(90)),
                callee=Identifier(position=Position(unique=offset(90)), name="pow"),
                arguments=[],
            ),
        )
    ],
)
