"""class TrafficLight(Module):
    def types(self):
        self.red = Boolean()
        self.green = Boolean()

    def locals(self):
        pass

    def inputs(self):
        pass

    def outputs(self):
        pass

    def shared_vars(self):
        pass

    def instances(self):
        pass

    def init(self):
        self.red = Boolean(True)
        self.green = Boolean(False)

    def next(self):
        self.red = ~self.green
        self.green = ~self.red

    def specification(self):
        return And(self.red.implies(~self.green), self.green.implies(~self.red))
"""
