class ITE(Module):
  def outputs(self):
    self.out = BitVector(1)

  def next(self):
    self.out = BitVector(0, 1) if True else BitVector(1, 1)

