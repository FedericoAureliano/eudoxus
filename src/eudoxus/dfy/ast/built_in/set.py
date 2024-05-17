from eudoxus.ast.expression import Add, Application, Equal, Integer
from eudoxus.ast.node import Identifier, Position
from eudoxus.ast.type import Integer as IntegerType
from eudoxus.dfy.ast.expression import Ite, Slice, Subscript
from eudoxus.dfy.ast.list_and_sets import ListType, Set, SetType
from eudoxus.dfy.ast.module import DfyModule
from eudoxus.dfy.ast.params import Param, Params

set_src = """import dafnypy
from typing import List, Set

@dafnypy.verify
def cast_to_set(l: List[int]) -> Set[int]:
    return set() if len(l) == 0 else cast_to_set(l[1:]) + {{l[0]}}
"""


def offset(x: int) -> int:
    return x - 2000


SetModule = DfyModule(
    position=Position(unique=offset(45)),
    method_or_function="function",
    name=Identifier(position=Position(unique=offset(65)), name="cast_to_set"),
    params=Params(
        position=Position(unique=offset(76)),
        params=[
            Param(
                position=Position(unique=offset(77)),
                type=ListType(
                    position=Position(unique=offset(80)),
                    element=IntegerType(position=Position(unique=offset(85))),
                ),
                name=Identifier(position=Position(unique=offset(77)), name="l"),
            )
        ],
    ),
    return_type=SetType(
        position=Position(unique=offset(94)),
        element=IntegerType(position=Position(unique=offset(98))),
    ),
    ret_name=None,
    body=Ite(
        position=Position(unique=offset(115)),
        condition=Application(
            position=Position(unique=offset(124)),
            callee=Equal(position=Position(unique=offset(124))),
            arguments=[
                Application(
                    position=Position(unique=offset(124)),
                    callee=Identifier(
                        position=Position(unique=offset(124)), name="len"
                    ),
                    arguments=[
                        Application(
                            position=Position(unique=offset(128)),
                            callee=Identifier(
                                position=Position(unique=offset(128)), name="l"
                            ),
                            arguments=[],
                        )
                    ],
                ),
                Integer(position=Position(unique=offset(134)), value=0),
            ],
        ),
        then_expr=Set(position=Position(unique=offset(115)), content=None),
        else_expr=Application(
            position=Position(unique=offset(141)),
            callee=Add(position=Position(unique=offset(141))),
            arguments=[
                Application(
                    position=Position(unique=offset(141)),
                    callee=Identifier(
                        position=Position(unique=offset(141)), name="cast_to_set"
                    ),
                    arguments=[
                        Subscript(
                            position=Position(unique=offset(153)),
                            list_value=Application(
                                position=Position(unique=offset(153)),
                                callee=Identifier(
                                    position=Position(unique=offset(153)), name="l"
                                ),
                                arguments=[],
                            ),
                            subscript=Slice(
                                position=Position(unique=offset(155)),
                                start=Integer(
                                    position=Position(unique=offset(155)), value=1
                                ),
                                end=None,
                                step=None,
                            ),
                        )
                    ],
                ),
                Set(
                    position=Position(unique=offset(162)),
                    content=[
                        Subscript(
                            position=Position(unique=offset(163)),
                            list_value=Application(
                                position=Position(unique=offset(163)),
                                callee=Identifier(
                                    position=Position(unique=offset(163)), name="l"
                                ),
                                arguments=[],
                            ),
                            subscript=Integer(
                                position=Position(unique=offset(165)), value=0
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
