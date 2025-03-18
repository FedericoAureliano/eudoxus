"""class VendingMachine(Module):
    def init(self):
        self.nsoda = BitVectorVal(0, 32)
        self.nbeer = BitVectorVal(0, 32)

    def next(self):
        self.action_sget = self.sget and (self.nsoda > BitVectorVal(0, 32))
        self.action_bget = self.bget and (self.nbeer > BitVectorVal(0, 32))
        self.nsoda = self.max if self.action_refill else self.nsoda
        self.nbeer = self.max if self.action_refill else self.nbeer

    def specification(self):
        return And(self.action_bget, self.action_refill, self.action_sget, self.nbeer)
"""
