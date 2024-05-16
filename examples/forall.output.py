class Forall(Module):
    def locals(self):
        self.x = int
        self.y = int

    def specification(self):
        return Forall(self.x1, bool, Implies(self.x1, self.y == 100))
