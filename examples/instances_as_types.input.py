class A(Module):
    def locals(self):
        self.x = int

class main(Module):
    def locals(self):
        self.a = A()
