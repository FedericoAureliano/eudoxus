import ast
import inspect

from .printer import UclidPrinter


class Module:
    """An abstract class to represent a UCLID5 module."""

    def types(self):
        """(Optional) Defines the type declarations.
        For example, the following implementation defines a 8-bit type called T:
        ```
        def types(self):
            self.T = BitVector(8)
        ```
        """
        pass

    def state(self):
        """(Optional) Defines the state variables and their types.
        For example, the following implementation defines an 8-bit variable x
        and an integer variable y:
        ```
        def state(self):
            self.x = BitVector(8)
            self.y = Integer()
        ```
        """
        pass

    def init(self):
        """(Optional) Defines how state variables are initialized.
        For example, the following implementation initializes x to 0 and y to 1:
        ```
        def init(self):
            self.x = 0
            self.y = 1
        ```
        """
        pass

    def next(self):
        """(Optional) Defines the transition relation.
        For example, the following implementation increments x and decrements y:
        ```
        def next(self):
            self.x = self.x + 1
            self.y = self.y - 1
        ```
        """
        pass

    def specification(self):
        """(Optional) Defines the specification in terms of invariant properties.

        Returns:
            bool: True if the specification is satisfied, False otherwise.

        For example, the following implementation defines two invariants:
        ```
        def specification(self):
            return self.x < 10 and self.y > 0
        """
        pass

    def proof(self):
        """(Optional) Defines the control block.
        For example, the following implementation uses 1-induction to prove
        that the specification always holds:
        ```
        def proof(self):
            induction(1)
        ```
        """
        pass

    def __str__(self) -> str:
        """Returns the UCLID5 representation of the Python class."""
        tree = ast.parse(inspect.getsource(self.__class__))
        return UclidPrinter().visit(tree)

    def execute(self, k: int) -> str:
        """Executes the module for k steps."""
        self.init()
        for _ in range(k):
            self.next()
