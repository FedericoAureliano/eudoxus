class Test(Module):
    def some_wild_func(self):
        assert self.types()  # some wild statement

    def types(self):
        self.T = bool
        self.U = bool

    def locals(self):
        self.x = self.T
        self.y = self.U

    def init(self):
        if self.x:
            self.x = self.y
        else:
            self.y = self.x
