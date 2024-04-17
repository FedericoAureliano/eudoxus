class ModuleWithVarAndInitAndInvariants(Module):
    def locals(self):
        self.x = int

    def init(self):
        self.x = 0

    def next(self):
        self.x = self.x + 1

    def specification(self):
        return self.x >= 0 and self.x <= 10
