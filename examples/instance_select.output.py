class A(Module):
    def inputs(self):
        self.x = int

    def outputs(self):
        self.y = int

class main(Module):
    def locals(self):
        self.x = int
        self.y = int

    def instances(self):
        self.a = A(x=self.x, y=self.y)

    def next(self):
        assert self.a.x == self.x