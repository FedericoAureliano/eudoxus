class BVAlt(Module):
    def sharedvars(self):
        self.x = BV(4)

    def next(self):
        self.x = BitVectorVal(4)(0)