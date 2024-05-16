class A(Module):
    def inputs(self):
        self.x = int
    def outputs(self):
        self.y = int

class main(Module):
    def instances(self):
        self.a = A(x=??, y=??)