class ModuleM(Module):
    def inputs(self):
        self.a = Integer()

    def outputs(self):
        self.b = Integer()


class main(Module):
    def locals(self):
        self.x = Integer()
        self.y = Integer()

    def instances(self):
        self.m = ModuleM(a=self.x, b=self.y)
