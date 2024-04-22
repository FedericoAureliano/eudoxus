class AltEnum(Module):
    def types(self):
        self.t1 = Enum("A", "B", "C")
        self.t2 = Enum("X", "Y", "Z")
