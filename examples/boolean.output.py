class Boolean(Module):
    def locals (self):
        self.x = int
        self.y = int

    def specification(self):
        return self.y == self.x or self.x <= 0 or self.x >= 10 and self.x != 5 and not self.x == 7