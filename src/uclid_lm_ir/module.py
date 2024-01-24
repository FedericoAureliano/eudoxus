import ast
import inspect

from .compiler import compile_to_uclid5


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

    def locals(self):
        """(Optional) Defines the local variables and their types.
        For example, the following implementation defines an 8-bit variable x
        and an integer variable y:
        ```
        def locals(self):
            self.x = BitVector(8)
            self.y = Integer()
        ```
        """
        pass

    def inputs(self):
        """(Optional) Defines the input variables and their types.
        For example, the following implementation defines an input variable x,
        which is an array of 8-bit bitvectors indexed by 2-bit bitvectors:
        ```
        def inputs(self):
            self.x = Array(BitVector(2), BitVector(8))
        ```
        """
        pass

    def outputs(self):
        """(Optional) Defines the output variables and their types.
        For example, the following implementation defines an output variable y,
        which is a real number:
        ```
        def outputs(self):
            self.y = Real()
        ```
        """
        pass

    def shared_vars(self):
        """(Optional) Defines the shared variables and their types.
        For example, the following implementation defines a shared variable z,
        which is an array of booleans indexed by integers:
        ```
        def shared_vars(self):
            self.z = Array(Integer(), Boolean())
        ```
        """
        pass

    def instances(self):
        """(Optional) Defines the instances of other modules and relates their
        input, output, and shared variables to local variables. Every instance
        variable must be related to a local variable. For example, let M be
        another module with inputs x and y, and output z. The following
        implementation defines an instance of M called m, and connects M's
        input variable x to the local variable self.a, M's input variable y to
        the local variable self.b, and M's output variable z to the local
        variable self.c:
        ```
        def instances(self):
            self.m = M(x=self.a, y=self.b, z=self.c)
        ```
        """
        pass

    def init(self):
        """(Optional) Defines how variables are initialized.
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
        return compile_to_uclid5(tree)

    def execute(self, k: int) -> str:
        """Executes the module for k steps."""
        self.init()
        for _ in range(k):
            self.next()
