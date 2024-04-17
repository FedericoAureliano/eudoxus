class HavocAssumeAssert(Module):
    def locals(self):
        self.x = Integer()

    def next(self):
        havoc(self.x)
        assume(self.x >= 0)
        assert self.x >= 110

    def specification(self):
        return self.x >= 100
