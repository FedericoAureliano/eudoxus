class BVAlt(Module):
    def sharedvars(self):
        self.x = BitVector(4)

    def next(self):
        self.x = BitVector(0, 4)