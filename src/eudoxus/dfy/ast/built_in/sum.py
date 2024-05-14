from eudoxus.ast.expression import Add, Application, Equal, Integer
from eudoxus.ast.node import Identifier, Position
from eudoxus.ast.type import Integer as IntegerType
from eudoxus.dfy.ast.expression import Ite, Slice, Subscript
from eudoxus.dfy.ast.list import List as ListType
from eudoxus.dfy.ast.module import DfyModule
from eudoxus.dfy.ast.params import Param, Params

sum_src = """from typing import List
import dafnypy

@dafnypy.verify
def sum(n: List[int]) -> int:
    return 0 if len(n) == 0 else n[0]  + sum(n[1:])
"""

SumModule = DfyModule(
    position=Position(unique=40),
    method_or_function="function",
    name=Identifier(position=Position(unique=60), name="sum"),
    params=Params(
        position=Position(unique=63),
        params=[
            Param(
                position=Position(unique=64),
                type=ListType(
                    position=Position(unique=67),
                    element=IntegerType(position=Position(unique=72)),
                ),
                name=Identifier(position=Position(unique=64), name="n"),
            )
        ],
    ),
    return_type=IntegerType(position=Position(unique=81)),
    body=Ite(
        position=Position(unique=97),
        condition=Application(
            position=Position(unique=102),
            callee=Equal(position=Position(unique=102)),
            arguments=[
                Application(
                    position=Position(unique=102),
                    callee=Identifier(position=Position(unique=102), name="len"),
                    arguments=[
                        Application(
                            position=Position(unique=106),
                            callee=Identifier(position=Position(unique=106), name="n"),
                            arguments=[],
                        )
                    ],
                ),
                Integer(position=Position(unique=112), value=0),
            ],
        ),
        then_expr=Integer(position=Position(unique=97), value=0),
        else_expr=Application(
            position=Position(unique=119),
            callee=Add(position=Position(unique=119)),
            arguments=[
                Subscript(
                    position=Position(unique=119),
                    list_value=Application(
                        position=Position(unique=119),
                        callee=Identifier(position=Position(unique=119), name="n"),
                        arguments=[],
                    ),
                    subscript=Integer(position=Position(unique=121), value=0),
                ),
                Application(
                    position=Position(unique=127),
                    callee=Identifier(position=Position(unique=127), name="sum"),
                    arguments=[
                        Subscript(
                            position=Position(unique=131),
                            list_value=Application(
                                position=Position(unique=131),
                                callee=Identifier(
                                    position=Position(unique=131), name="n"
                                ),
                                arguments=[],
                            ),
                            subscript=Slice(
                                position=Position(unique=133),
                                start=Integer(position=Position(unique=133), value=1),
                                end=None,
                                step=None,
                            ),
                        )
                    ],
                ),
            ],
        ),
    ),
    requires=[],
    ensures=[],
)
