class Undefined(Module):
    def types(self):
        self.O = int
        self.T = self.O
    
    def locals(self):
        self.y = int

    def sharedvars(self):
        self.x = self.T

    def next(self):
        self.x = self.y