class Random(Module):
    def locals(self):
        self.x = int
        self.y = bool

    def init(self):
        self.nondet_1 = int
        self.nondet_2 = bool
        self.nondet_3 = Real()
        self.nondet_4 = bool

        self.x = self.nondet_1
        self.y = self.nondet_2

        if self.nondet_3 < 0.5:
            self.x = 1

        if self.nondet_4:
            self.y = False