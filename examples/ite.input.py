class ITE(Module):
    def outputs(self):
        self.out = BV(1)

    def next(self):
        self.out = ite(True, BV(0, 1), BV(1, 1))