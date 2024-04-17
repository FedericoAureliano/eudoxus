class HavocAssumeAssert(Module):
    def locals(self):
        self.x = int

    def next(self):
        Havoc(self.x)
        Assume(self.x >= 0)
        assert self.x >= 110

    def specification(self):
        return self.x >= 100
