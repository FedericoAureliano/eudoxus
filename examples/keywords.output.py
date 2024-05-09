class Keywords(Module):
    def types(self):
        self.integer = int
    
    def outputs(self):
        self.x = int
    
    def specification(self):
        return self.x == 5