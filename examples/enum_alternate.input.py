class AltEnum(Module):
    def types(self):
        self.t1 = Enum('AltEnum', ['A', 'B', 'C'])
        self.t2 = Enum('t2', 'X', 'Y', 'Z')
