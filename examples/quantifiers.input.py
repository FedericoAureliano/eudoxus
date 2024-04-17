class Quantifiers(Module):
    def locals(self):
        self.x = Integer()

    def next(self):
        assert exists([(x, Integer())], x > 0)
        assert forall([(x, Integer())], x < 10)
