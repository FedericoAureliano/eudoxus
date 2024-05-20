class Enumeration(Module):
    def types(self):
        self.Color = Enum("blue", "green", "red")
        self.Other = Enum("b", "g", "r")
        self.Other2 = Enum("anon_enum_0", "anon_enum_1", "anon_enum_2", "anon_enum_3")
        self.Other3 = Enum("anon_enum_4")

    def locals(self):
        self.color = self.Color
        self.other = self.Other()
        self.other2 = self.Other2()
        self.other3 = self.Other3()

    def init(self):
        self.color = "red"

    def next(self):
        self.color = "green"

    def specification(self):
        return self.color != "blue"
