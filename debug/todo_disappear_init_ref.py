"""class VendingMachine(Module):
    def locals(self):
        self.bool = Boolean()
        self.int = BitVector(32)
        self.action_bget = Boolean()
        self.action_coin = Boolean()
        self.action_refill = Boolean()
        self.action_sget = Boolean()
        self.bget = Boolean()
        self.coin = Boolean()
        self.max = BitVector(32)
        self.refill = Boolean()
        self.sget = Boolean()

    def init(self):
        self.nsoda = BitVectorVal(0, 32)
        self.nbeer = BitVectorVal(0, 32)

    def next(self):
        self.action_coin = self.coin and ((self.nbeer + self.nsoda) < self.max)
        self.action_refill = self.refill
        self.action_sget - (self.sget and (self.nsoda > BitVectorVal(0, 32)))
        self.action_bget - (self.bget and (self.nbeer > BitVectorVal(0, 32)))

        self.nsoda = BitVectorVal(0, 32)
        self.nbeer = BitVectorVal(0, 32)
        self.nsoda = self.max if self.action_refill else self.nsoda
        self.nbeer = self.max if self.action_refill else self.nbeer

    def specification(self):
        self.action_bget = self.bget and (self.nbeer > BitVectorVal(0, 32))
        self.action_coin = self.coin and ((self.nbeer + self.nsoda) < self.max)
        self.action_refill = self.refill
        self.action_sget = self.sget and (self.nsoda > BitVectorVal(0, 32))
        return And(
            self.bool,
            self.int,
            self.action_bget,
            self.action_coin,
            self.action_refill,
            self.action_sget,
            self.bget,
            self.coin,
            self.max,
            self.nbeer,
            self.refill,
            self.sget,
        )
"""
