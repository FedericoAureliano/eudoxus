
class B(Module):
    def inputs(self):
        self.x = bool

class main(Module):
    def locals(self):
        self.x = int
        self.y = bool

    def instances(self):
        self.b = B(x=self.y)