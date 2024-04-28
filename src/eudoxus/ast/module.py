from dataclasses import dataclass

import eudoxus.ast.expression as e
import eudoxus.ast.proof as p
import eudoxus.ast.statement as s
from eudoxus.ast.node import Identifier, Node


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
    specification: e.Expression
    control: p.Command
