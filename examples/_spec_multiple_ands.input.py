class TrafficLight(Module):
    def locals(self):
        self.red = Boolean()
        self.green = Boolean()
        self.yellow = Boolean()

    def next(self):
        self.red = self.yellow
        self.yellow = self.green
        self.green = Xor(self.yellow, self.green)

    def specification(self):
        return And(
            Implies(self.red, self.yellow),
            Implies(self.yellow, self.red),
            Implies(self.green, self.yellow),
            Implies(self.red, self.yellow),
        )
