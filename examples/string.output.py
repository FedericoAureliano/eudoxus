class String(Module):
    def types(self):
        self.str = Enum("??")

    def locals(self):
        self.s = self.str

    def init(self):
        self.s = "Hello, World!"

    def next(self):
        if self.s == "Hello, World!":
            self.s = "Goodbye, World!"