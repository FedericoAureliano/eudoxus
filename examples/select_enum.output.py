class SelectEnum(Module):
    def types(self):
        self.color = Enum("BLUE", "GREEN", "RED")

    def locals(self):
        self.x = self.color

    def init (self):
        self.x = "RED"