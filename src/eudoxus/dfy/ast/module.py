from dataclasses import dataclass
from typing import List

import eudoxus.ast.statement as s
import eudoxus.ast.type as t
import eudoxus.dfy.ast.params as p
from eudoxus.ast import expression as e
from eudoxus.ast.node import Identifier, Node
from eudoxus.dfy.ast.statement import Ensures, Requires


@dataclass(frozen=True)
class DfyModule(Node):
    method_or_function: str | None
    name: Identifier
    params: List[p.Params]
    return_type: t.Type
    ret_name: Identifier | None
    body: s.Block | e.Expression
    requires: List[Requires]
    ensures: List[Ensures]
