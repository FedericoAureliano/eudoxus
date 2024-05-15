class Xor(Module):
    def locals(self):
        self.x = bool
        self.y = bool

    def init(self):
        self.x = 0
        self.y = 0

    def next(self):
        self.x = self.x xor self.y
        self.y = Xor(self.x, self.y)