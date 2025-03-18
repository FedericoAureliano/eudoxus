class TrafficLight(Module):
    def locals(self):
        self.red = Boolean()
        self.green = Boolean()
        self.yellow = Boolean()

    def init(self):
        self.red = Boolean(False)
        self.green = Boolean(False)
        self.yellow = Boolean(True)

    def next(self):
        self.red = self.yellow
        self.yellow = self.green
        self.green = self.red

    def specification(self):
        return And(
            Implies(self.red, self.yellow),
            Implies(self.yellow, self.red),
            Implies(self.green, self.yellow),
            Implies(self.red, Next(self.yellow)),
        )
