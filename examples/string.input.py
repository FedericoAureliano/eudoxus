class String(Module):
    def locals(self):
        self.s = str

    def init(self):
        self.s = "Hello, World!"

    def next(self):
        if self.s == "Hello, World!":
            self.s = "Goodbye, World!"