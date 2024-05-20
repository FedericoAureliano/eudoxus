class Arithmetic(Module):
    def locals(self):
        self.x = int

    def init(self):
        self.x = self.x * 2 if self.x / 2 == 0 else self.x + 1
        self.x = self.x / self.x - self.x