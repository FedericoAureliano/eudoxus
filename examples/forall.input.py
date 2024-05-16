class Forall(Module):
    def locals(self):
        self.x = Integer()
        self.y = Integer()

    def specification(self):
        return ForAll(self.x, Implies(self.x, self.y == 100))
