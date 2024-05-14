class Undefined:
    def types(self):
        self.T = self.O

    def sharedvars(self):
        self.x = self.T

    def next(self):
        self.x = Implies(self.y <= 0 or False, True)