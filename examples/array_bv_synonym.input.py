class M(Module):
    def types(self):
        self.T = BitVector(8)

    def locals(self):
        self.x = Array(index=BitVector(8), value=self.T)
