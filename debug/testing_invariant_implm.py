class VendingMachine(Module):
    def locals(self):
        self.max = int
        self.nbeer = int
        self.nsoda = int
        self.sget = bool
        self.bget = bool
        self.refill = bool
        self.coin = bool
        self.ret_coin = bool

    def init(self):
        self.nsoda = self.max
        self.nbeer = self.max
        self.sget = False
        self.bget = False
        self.refill = False
        self.coin = True
        self.ret_coin = False

    def next(self):
        if (self.nsoda > 0) and (self.nbeer > 0):
            self.sget = True
            self.bget = True
        else:
            self.sget = False
            self.bget = False
        if (self.nsoda == 0) and (self.nbeer == 0):
            self.ret_coin = True
            self.coin = False
        else:
            self.ret_coin = False
            self.coin = True
        if self.sget:
            self.nsoda = self.nsoda - 1
        if self.bget:
            self.nbeer = self.nbeer - 1
        if self.refill:
            self.nsoda = self.max
            self.nbeer = self.max

    def specification(self):
        self.nsoda_inv = (self.nsoda >= 0) and (self.nsoda <= self.max)
        self.nbeer_inv = (self.nbeer >= 0) and (self.nbeer <= self.max)
        self.sget_inv = Implies((self.nsoda > 0), self.sget)
        self.bget_inv = Implies((self.nbeer > 0), self.bget)
        self.refill_inv = Implies(
            ((self.nsoda < self.max) or (self.nbeer < self.max)), self.refill
        )
        self.coin_inv = self.coin == True
        self.ret_coin_inv = Implies(
            ((self.nsoda == 0) and (self.nbeer == 0)), self.ret_coin
        )
        return self.ret_coin_inv and (
            self.coin_inv
            and (
                self.refill_inv
                and (
                    self.bget_inv
                    and (self.sget_inv and (self.nsoda_inv and self.nbeer_inv))
                )
            )
        )
