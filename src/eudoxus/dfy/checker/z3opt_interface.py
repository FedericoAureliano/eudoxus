from typing import Dict, List, Tuple

import z3

from eudoxus.ast.module import Module
from eudoxus.ast.node import Node, Position


class Checker:
    def __init__(self) -> None:
        z3.set_option("smt.random_seed", 0)
        self.opt_solver = z3.Optimize()
        self.opt_solver.set("maxsat_engine", "pd-maxres")
        self.soft_constraints = set()

    def check(self, modules: List[Module]) -> List[Dict[Position, Node]]:
        raise NotImplementedError("Implement this method in a subclass!")

    def reason_to_weight(self, reason: str) -> int:
        raise NotImplementedError("Implement this method in a subclass!")

    def declare_sort(self, name: str) -> z3.SortRef:
        return z3.DeclareSort(name)

    def declare_function(self, name: str, *args: z3.SortRef) -> z3.FuncDeclRef:
        return z3.Function(name, *args)

    def declare_constant(self, name: str, sort: z3.SortRef) -> z3.ExprRef:
        return z3.Const(name, sort)

    def fresh_constant(self, sort: z3.SortRef, prefix="") -> z3.ExprRef:
        return z3.FreshConst(sort, prefix)

    def add_all_diff_hard(self, terms, position):
        self.add_soft_constraint(z3.Distinct(*terms), position, "hard")

    def add_soft_constraint(
        self, constraint: z3.ExprRef, pos: Position, reason: str
    ) -> None:
        self.soft_constraints.add((pos, reason, constraint))

    def add_conflict(self, pos: Position) -> None:
        self.add_soft_constraint(z3.BoolVal(False), pos)

    def get_depth(self, expr):
        def get_depth_rec(expr, depth):
            if z3.is_const(expr):
                return depth
            else:
                return max(get_depth_rec(arg, depth + 1) for arg in expr.children())

        return get_depth_rec(expr, 0)

    def solve(self) -> Tuple[List[Position], z3.ModelRef]:
        """
        Check the constraints and return the list of positions that need to be
        changed and a model for inference.
        """
        self.opt_solver.push()

        for p, r, c in sorted(list(self.soft_constraints), key=str):
            weight = self.reason_to_weight(r)
            self.opt_solver.add_soft(c, weight=weight)

        result = self.opt_solver.check()  # should always be sat
        assert result == z3.sat
        model = self.opt_solver.model()
        self.opt_solver.pop()

        positions = []
        for p, r, c in self.soft_constraints:
            if model.eval(c) == z3.BoolVal(False):
                # print(f"(off)\t{c}")
                positions.append(p)
            # else:
            #     print(f"(on)\t{c}")

        return (positions, model)
