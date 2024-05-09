class Boolean(Module):
    def locals (self):
        self.x = real()
        self.y = int()

    def spec(self):
        return ((self.y == self.x or self.x <= 0) or (self.x >= 10 and self.x != 5 and not self.x == 7.0))