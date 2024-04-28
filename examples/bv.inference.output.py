class M(Module):
    def locals(self):
        self.x = BitVector(8)

    def init(self):
        self.x = self.x + BitVectorVal(1, 8)
