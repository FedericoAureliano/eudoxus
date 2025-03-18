"""class Module(Module):
    def locals(self):
        self.max = int
        self.bget = bool
        self.coin = bool
        self.coin_allowed = bool
        self.nbeer = int
        self.nsoda = int
        self.refill = bool
        self.sget = bool

    def init(self):
        self.nsoda = 0
        self.nbeer = 0
        self.coin_allowed = False

    def next(self):
        if self.coin:
            if ((self.nsoda > 0) or (self.nbeer > 0)):
            self.coin_allowed = True
        if self.refill:
            self.nsoda = 16
            self.nbeer = 16
            self.coin_allowed = False
        if self.sget:
            if (self.nsoda > 0):
            self.nsoda = (self.nsoda - 1)
        if self.bget:
            if (self.nbeer > 0):
            self.nbeer = (self.nbeer - 1)
        if ((self.nsoda == 0) and (self.nbeer == 0)):
            self.coin_allowed = False

    def specification(self):
        self.inv1 = (self.nsoda >= 0)
        self.inv2 = (self.nbeer >= 0)
        self.inv3 = (self.coin_allowed == ((self.nsoda > 0) or (self.nbeer > 0)))
        self.inv4 = (self.sget => (self.nsoda' == self.nsoda - 1)) and \
            (self.bget => (self.nbeer' == self.nbeer - 1))
        self.inv5 = (self.sget => (self.nsoda > 0)) and (self.bget => \
            (self.nbeer > 0))
        self.inv6 = (self.ret_coin => (self.nsoda' == 0) and (self.nbeer' == 0))
        self.inv7 = (self.refill => (self.nsoda' == self.max) and \
            (self.nbeer' == self.max))
        return (self.inv7 and (self.inv6 and (self.inv5 and (self.inv4\
              and (self.inv3 and (self.inv1 and self.inv2))))))
"""
