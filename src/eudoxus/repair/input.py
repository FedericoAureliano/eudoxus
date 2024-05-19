from typing import Dict, List

import eudoxus.ast.module as m
import eudoxus.ast.statement as s
from eudoxus.ast.node import Identifier, Node, Position
from eudoxus.repair.interface import Checker


class InputChecker(Checker):
    """
    Find when a variable is declared as an input but is written to
    """

    def __init__(self):
        self.position = -7000

    def fpos(self):
        self.position -= 1
        return Position(self.position)

    def enter_input(self, node):
        match node:
            case s.Assignment(_, lhs, _):
                lhs.traverse(self.enter_lhs, self.exit_lhs)

    def enter_lhs(self, node):
        match node:
            case Identifier(_, name):
                self.written.append(name)

    def exit_input(self, _):
        pass

    def exit_lhs(self, _):
        pass

    def check(self, modules: List[m.Module]) -> List[Dict[Position, Node]]:
        rewrites = []

        for module in modules:
            self.written = []
            module.traverse(self.enter_input, self.exit_input)

            new_inputs = []
            for input in module.inputs.statements:
                if input.target.name not in self.written:
                    new_inputs.append(input)

            new_block = s.Block(self.fpos(), new_inputs)
            rwr = {}
            input_pos = module.inputs.position
            rwr[input_pos] = new_block
            rewrites.append(rwr)

        return rewrites
