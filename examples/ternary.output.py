class Ternary(Module):
    def inputs(self):
        self.x = BitVector(2)

    def outputs(self):
        self.y = BitVector(1)

    def next(self):
        self.y = BitVectorVal(1, 1) if self.x == BitVectorVal(1, 2) else BitVectorVal(0, 1)
