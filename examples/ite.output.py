class ITE(Module):
  def outputs(self):
    self.out = BitVector(1)

  def next(self):
    self.out = BitVectorVal(0, 1) if True else BitVectorVal(1, 1)

