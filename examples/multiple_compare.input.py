class MultipleCompare(Module):
    def locals(self):
        self.x = Int()

    def next(self):
        assert self.x > self.x + 1 > self.x + 2 > self.x + 3
