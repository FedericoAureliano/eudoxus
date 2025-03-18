"""class BeverageVendingMachine(Module):
    def locals(self):
        self.bget = bool
        self.coin = bool
        self.max = int
        self.nbeer = int
        self.nsoda = int
        self.refill = bool
        self.sget = bool

    def init(self):
        self.nsoda = 5
        self.nbeer = 5
        self.sget = self.nsoda > 0
        self.bget = self.nbeer > 0
        self.refill = False
        self.coin = True

    def next(self):
        if self.coin:
            self.coin = True
        else:
            if self.refill:
                self.nsoda = self.max
                self.nbeer = self.max
            else:
                if self.sget:
                    self.nsoda = self.nsoda - 1
                else:
                    if self.bget:
                        self.nbeer = self.nbeer - 1
        if (self.nsoda == 0) and (self.nbeer == 0):
            self.coin = True
        else:
            self.coin = False

    def specification(self):
        return (self.coin == True) and (
            (self.coin == True)
            and (
                (self.bget == ((self.nbeer > 0) and ((self.nbeer - 1) > 0)))
                and (
                    (self.sget == ((self.nsoda > 0) and ((self.nsoda - 1) > 0)))
                    and (
                        (
                            self.refill
                            == ((self.nsoda == self.max) and (self.nbeer == self.max))
                        )
                        and (
                            (((self.nsoda == 0) and (self.nbeer == 0)) == self.coin)
                            and (
                                (self.nbeer <= self.max)
                                and (
                                    (self.nsoda <= self.max)
                                    and ((self.nsoda >= 0) and (self.nbeer >= 0))
                                )
                            )
                        )
                    )
                )
            )
        )
"""
