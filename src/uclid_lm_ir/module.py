import ast
import inspect

from .printer import UclidPrinter


class Module:
    def init(self):
        """
        The initialization block of a UCLID5 module.
        """
        raise NotImplementedError("init not implemented")

    def next(self):
        """
        The transition relation of a UCLID5 module.
        """
        raise NotImplementedError("init not implemented")

    def control(self):
        """
        The control block of a UCLID5 module.
        """
        raise NotImplementedError("init not implemented")

    def __str__(self) -> str:
        tree = ast.parse(inspect.getsource(self.__class__))
        return UclidPrinter().visit(tree)

    def execute(self, k: int) -> str:
        """
        Execute the module for k steps.
        """
        self.init()
        for _ in range(k):
            self.next()
