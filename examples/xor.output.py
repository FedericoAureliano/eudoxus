class Xor(Module):
    def locals(self):
        self.x = bool
        self.y = bool

    def init(self):
        self.x = False
        self.y = False

    def next(self):
        self.x = ??
        self.y = Xor(self.x, self.y)