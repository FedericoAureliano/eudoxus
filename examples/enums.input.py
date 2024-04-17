class Enumeration:
    def types(self):
        self.Color = Enumeration("red", "green", "blue")
        self.Other = Enumeration(["r", "g", "b"])
        self.Other2 = Enumeration(4)
        self.Other3 = Enumeration(1)

    def locals(self):
        self.color = self.Color()

    def init(self):
        self.color = "red"

    def next(self):
        self.color = "green"

    def specification(self):
        return self.color != "blue"
