from dataclasses import dataclass
from typing import List

from eudoxus.ast.node import Identifier, Node
from eudoxus.ast.type import Type


@dataclass(frozen=True)
class Param(Node):
    type: Type
    name: Identifier


@dataclass(frozen=True)
class Params(Node):
    params: List[Param]

    def __len__(self):
        return len(self.params)
