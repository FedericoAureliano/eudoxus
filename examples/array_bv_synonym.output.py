class M(Module):
    def types(self):
        self.T = BitVector(8)

    def locals(self):
        self.x = Array(BitVector(8), self.T)
