from dataclasses import dataclass

import eudoxus.ast.expression as e
import eudoxus.ast.proof as p
import eudoxus.ast.statement as s
from eudoxus.ast.node import Identifier, Node


@dataclass(frozen=True)
class Module(Node):
    name: Identifier
    types: s.Block
    locals: s.Block
    inputs: s.Block
    outputs: s.Block
    sharedvars: s.Block
    instances: s.Block
    init: s.Block
    next: s.Block
    specification: e.Expression
    control: p.Command
