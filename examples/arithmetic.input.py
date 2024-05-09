class Arithmetic(Module):
    def locals(self):
        self.x = Integer()

    def init(self):
        self.x = If(self.x % 2 == 0, self.x * 2, self.x + 1)
        self.x = self.x / self.x - self.x