class A(Module):
    def locals(self):
        self.x = int

class main(Module):
    def instances(self):
        self.a = A()
