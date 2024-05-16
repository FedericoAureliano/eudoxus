class Forall(Module):
    def locals(self):
        self.x = int
        self.y = int

    def specification(self):
        return Forall(self.x0, bool, Implies(self.x0, self.y == 100))
