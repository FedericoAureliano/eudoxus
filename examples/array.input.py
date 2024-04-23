class Arrays(Module):
    def inputs(self):
        self.x = Array(BitVector(32), BitVector(8))

    def locals(self):
        self.z = Array(int, int)

    def outputs(self):
        self.y = BitVector(8)

    def init(self):
        self.z[0] = 0

    def next(self):
        self.y = self.x[BitVectorVal(0, 32)]

    