class Ternary(Module):
    def inputs(self):
        self.x = BitVector(2)

    def outputs(self):
        self.y = BitVector(1)

    def next(self):
        self.y = 1 if self.x == BitVector(2, value=1) else 0
