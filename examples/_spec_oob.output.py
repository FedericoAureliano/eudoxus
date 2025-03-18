class TrafficLights(Module):
    def types(self):
        self.StateColor = BitVector(2)

    def locals(self):
        self.L1 = self.StateColor
        self.L2 = self.StateColor
        self.L3 = self.StateColor
        self.L4 = self.StateColor
        self.invariant1 = bool
        self.invariant2 = bool
        self.invariant3 = bool
        self.invariant4 = bool
        self.invariant5 = bool

    def init(self):
        self.L1 = 0
        self.L2 = 2
        self.L3 = 0
        self.L4 = 2

    def next(self):
        if ((self.L1 == 0) and (self.L3 == 0)):
            self.L1 = 1
            self.L3 = 1
        else:
            if ((self.L1 == 1) and (self.L3 == 1)):
                self.L1 = 2
                self.L3 = 2
                self.L2 = 0
            else:
                if (self.L2 == 0):
                    self.L2 = 1
                else:
                    if (self.L2 == 1):
                        self.L2 = 2
                        self.L4 = 0
                    else:
                        if (self.L4 == 0):
                            self.L4 = 1
                        else:
                            if (self.L4 == 1):
                                self.L4 = 2
                                self.L1 = 0
                                self.L3 = 0

    def specification(self):
        self.invariant1 = (self.L1 == 0) + (self.L2 == 0) + (self.L3 == 0) + (self.L4 == 0) == 1
        self.invariant2 = ((self.L1 == 0) & (self.L1 == 1) & (self.L1 == 2))
        self.invariant3 = (self.L1 == self.L3) & (self.L1 == 1)
        self.invariant4 = (self.L2 == 1) >> ((self.L1 != 1) & (self.L3 != 1))
        self.invariant5 = ~((self.L1 == 1) & (self.L2 == 1)) & ~((self.L3 == 1) & (self.L4 == 1)
        return self.invariant1 & self.invariant2 & self.invariant3 & self.invariant4 & self.invariant5
