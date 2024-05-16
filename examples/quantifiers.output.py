class Quantifiers(Module):
    def locals(self):
        self.x = int

    def next(self):
        assert Exists(self.x0, int, self.x0 > 0)
        assert Forall(self.x1, bool, self.x1)
