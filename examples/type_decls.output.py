class ModuleWithTypeDecls(Module):
    def types(self):
        self.T = int
        self.U = BitVector(32)

    def outputs(self):
        self.x = self.T
        self.y = self.U