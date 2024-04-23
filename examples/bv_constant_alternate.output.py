class BVAlt(Module):
    def sharedvars(self):
        self.x = BitVector(4)

    def next(self):
        self.x = BitVectorVal(0, 4)