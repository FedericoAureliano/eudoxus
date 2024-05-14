class Undefined(Module):
    def types(self):
        self.O = bool
        self.T = self.O
    
    def locals(self):
        self.y = int

    def sharedvars(self):
        self.x = self.T

    def next(self):
        self.x = Implies(self.y <= 0 or False, True)