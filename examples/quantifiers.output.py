class Quantifiers(Module):
    def locals(self):
        self.x = int

    def next(self):
        assert Exists([(self.x, int)], self.x > 0)
        assert Forall([(self.x, int)], self.x < 10)
