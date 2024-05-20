class Random(Module):
    def locals(self):
        self.nondet_1 = int
        self.nondet_2 = bool
        self.nondet_3 = Real()
        self.nondet_4 = bool
        self.x = int
        self.y = bool

    def init(self):
        Havoc(self.nondet_1)
        Havoc(self.nondet_2)
        Havoc(self.nondet_3)
        Havoc(self.nondet_4)

        self.x = self.nondet_1
        self.y = self.nondet_2

        if self.nondet_3 < 0.5:
            self.x = 1

        if self.nondet_4:
            self.y = False