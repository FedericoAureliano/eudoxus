class B(Module):
    def inputs(self):
        self.z = bool

class main(Module):
    def locals(self):
        self.x = int
        self.y = bool

    def instances(self):
        self.a = A()
        self.b = B(z=self.y)