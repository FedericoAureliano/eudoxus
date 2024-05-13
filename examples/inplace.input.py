class InPlace(Module):
    def outputs(self):
        self.x = int

    def init(self):
        self.x += 1
        self.x -= 1
        self.x *= 7
        self.x /= 3
        self.x %= 5