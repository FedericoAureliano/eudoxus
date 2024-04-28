class Quantifiers(Module):
    def locals(self):
        self.x = int

    def next(self):
        assert Exists(x, int, self.x > 0)
        assert Forall(x, int, self.x < 10)
