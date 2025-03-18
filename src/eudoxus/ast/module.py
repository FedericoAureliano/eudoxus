from dataclasses import dataclass
from typing import List, Tuple

import eudoxus.ast.expression as e
import eudoxus.ast.proof as p
import eudoxus.ast.statement as s
from eudoxus.ast.node import Identifier, Node


@dataclass(frozen=True)
class SpecBlock(Node):
    bindings: List[Tuple[Identifier, e.Expression]]
    specs: List[e.Expression]

    def is_empty(self):
        return len(self.specs) == 0


@dataclass(frozen=True)
class Module(Node):
    name: Identifier
    types: s.Statement
    locals: s.Statement
    inputs: s.Statement
    outputs: s.Statement
    sharedvars: s.Statement
    instances: s.Statement
    init: s.Statement
    next: s.Statement
    specification: SpecBlock
    control: p.Command

    def is_empty(self):
        return (
            self.types.is_empty()
            and self.locals.is_empty()
            and self.inputs.is_empty()
            and self.outputs.is_empty()
            and self.sharedvars.is_empty()
            and self.instances.is_empty()
            and self.init.is_empty()
            and self.next.is_empty()
            and self.specification.is_empty()
            and self.control.is_empty()
        )
