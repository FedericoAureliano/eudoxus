class InPlace(Module):
    def outputs(self):
        self.x = BitVector(2)

    def init(self):
        self.x = (self.x + BitVectorVal(1, 2))
        self.x = (self.x - BitVectorVal(1, 2))
        self.x = (self.x * BitVectorVal(7, 2))
        self.x = (self.x / BitVectorVal(3, 2))
        self.x = (self.x % BitVectorVal(5, 2))
