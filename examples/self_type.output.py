class SelfType(Module):
    def types(self):
        self.t = int

    def outputs(self):
        self.x = self.t