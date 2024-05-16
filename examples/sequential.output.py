class Sequential(Module):
    def locals(self):
        self.x = int
    
    def next(self):
        self.x = self.x + 1
        self.x = self.x - 1