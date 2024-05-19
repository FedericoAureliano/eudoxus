class Enumeration:
    def types(self):
        self.Color = Enumeration("red", "green", "blue")
        self.Other = Enumeration(["r", "g", "b"])
        self.Other2 = Enumeration(4)
        self.Other3 = Enumeration(1)

    def locals(self):
        self.color = self.Color()
        self.other = self.Other()
        self.other2 = self.Other2()
        self.other3 = self.Other3()

    def init(self):
        self.color = "red"

    def next(self):
        self.color = "green"

    def specification(self):
        return self.color != "blue"
