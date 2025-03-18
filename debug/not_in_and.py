"""class TrafficLight(Module):
    def locals(self):
        self.previous_state = Enum("yellow")
        self.green = bool()
        self.red = bool()
        self.yellow = bool()

    def init(self):
        self.green = False
        self.red = False
        self.yellow = False

    def next(self):
        self.yellow = self.green
        self.red = self.yellow
        self.green = not self.red
        self.previous_state = If(self.red, "yellow", self.previous_state)

    def specification(self):
        return And(
            Not(self.red) & Not(self.green), self.yellow
        )  # maybe this can be looked at if it continues being an issue
"""
