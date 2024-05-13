class InPlace(Module):
    def outputs(self):
        self.x = int

    def init(self):
        self.x = self.x + 1
        self.x = self.x - 1
        self.x = self.x * 7
        self.x = self.x / 3
        self.x = self.x % 5