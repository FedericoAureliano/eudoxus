from dataclasses import dataclass

# from eudoxus.ast import expression as e
from eudoxus.ast.type import Type


@dataclass(frozen=True)
class StringType(Type):
    pass
