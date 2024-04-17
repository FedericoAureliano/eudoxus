class ModuleM(Module):
    def inputs(self):
        self.a = int

    def outputs(self):
        self.b = int


class main(Module):
    def locals(self):
        self.x = int
        self.y = int

    def instances(self):
        self.m = ModuleM(a=self.x, b=self.y)
