class SelectEnum(Module):
    def types(self):
        self.color = Enum("RED", "GREEN", "BLUE")

    def locals(self):
        self.x = self.color

    def init (self):
        self.x = "RED"