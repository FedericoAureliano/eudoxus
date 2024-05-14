class MultipleCompare(Module):
    def locals(self):
        self.x = int

    def next(self):
        assert self.x > self.x + 1 and self.x + 1 >= self.x + 2 and self.x + 2 > self.x + 3
