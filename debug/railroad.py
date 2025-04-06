class RailroadCrossing(Module):
    def locals(self):
        self.train_state = Enum("far", "in", "near")
        self.controller_state = Enum("0", "1", "2", "3")
        self.gate_state = Enum("down", "up")

    def inputs(self):
        self.train_approach = bool
        self.train_exit = bool

    def outputs(self):
        self.gate_raise = bool

    def next(self):
        if (self.train_state == "far") and self.train_approach:
            self.controller_state = "1"
        if (self.train_state == "near") and (self.controller_state == "1"):
            self.controller_state = "2"
        if (self.train_state == "in") and self.train_exit:
            self.controller_state = "3"
        if self.controller_state == "2":
            self.controller_state = "3"
        if self.controller_state == "3":
            self.controller_state = "0"
        self.gate_raise = self.gate_state == "up"

    def specification(self):
        self.invariant1 = (self.train_state == "in") == (self.gate_state == "down")
        self.invariant2 = (self.train_state == "far") == (self.gate_state == "up")
        self.invariant3 = (self.controller_state == "0") == (self.train_state == "near")
        self.invariant4 = (self.controller_state == "2") == (self.train_state == "far")
        self.invariant5 = (
            (self.train_state == "far") and (self.gate_state == "up")
        ) and (self.controller_state == "0")
        return self.invariant1 and self.invariant2
