class A(Module):
    def inputs(self):
        self.x = int
    
    def outputs(self):
        self.y = int

    def next(self):
        havoc(self.y)
        assume(self.y > self.x)

class B(Module):
    def locals(self):
        self.c = int
        self.d = int

    def instances(self):
        self.a = A(x= self.c, y= self.d)
    
    def init(self):
        self.c = 1

    def next(self):
        self.a.next()
        assert(self.d > self.c)
