import ast
import inspect

from .printer import UclidPrinter


class Module:
    """An abstract class to represent a UCLID5 module."""

    def state(self):
        """Defines the state variables.
        For example, the following implementation defines two 8-bit variables x and y:
        ```
        def state(self):
            self.x = BitVector(8)
            self.y = BitVector(8)
        ```
        """
        raise NotImplementedError("state block not defined")

    def init(self):
        """Defines how state variables are initialized.
        For example, the following implementation initializes x to 0 and y to 1:
        ```
        def init(self):
            self.x = 0
            self.y = 1
        ```
        """
        raise NotImplementedError("init block not defined")

    def next(self):
        """Defines the transition relation.
        For example, the following implementation increments x and decrements y:
        ```
        def next(self):
            self.x = self.x + 1
            self.y = self.y - 1
        ```
        """
        raise NotImplementedError("next block not defined")

    def specification(self):
        """Defines the specification in terms of invariant properties.

        Returns:
            bool: True if the specification is satisfied, False otherwise.

        For example, the following implementation defines two invariants:
        ```
        def specification(self):
            return self.x < 10 and self.y > 0
        """
        raise NotImplementedError("specification block not defined")

    def proof(self):
        """Defines the control block.
        For example, the following implementation uses 2-induction to prove
        that the specification always holds:
        ```
        def proof(self):
            induction(2)
        ```
        """
        raise NotImplementedError("proof block not defined")

    def __str__(self) -> str:
        """Returns the UCLID5 representation of the Python class."""
        tree = ast.parse(inspect.getsource(self.__class__))
        return UclidPrinter().visit(tree)

    def execute(self, k: int) -> str:
        """Executes the module for k steps."""
        self.init()
        for _ in range(k):
            self.next()
