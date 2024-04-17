class Hole(Module):
    def locals(self):
        self.x = bool

    def init(self):
        if self.x:
            self.x = False
