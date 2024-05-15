class A(Module):
    def inputs(self):
        self.x = Integer()

    def outputs(self):
        self.y = Integer()

class main(Module):
    def locals(self):
        self.x = Integer()
        self.y = Integer()

    def instances(self):
        self.a = A(x=self.x, y=self.y)

    def next(self):
        assert self.a.x == self.x