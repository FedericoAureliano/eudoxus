class Quantifiers(Module):
    def locals(self):
        self.x = int

    def next(self):
        assert Exists(self.x1, int, self.x1 > 0)
        assert Forall(self.x1, int, self.x1 < 10)
