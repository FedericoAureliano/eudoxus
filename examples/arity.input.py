class Arity(Module):
    def specification(self):
        return And(Add(1) == Subtract(1) + Mult(7) - Div(3))