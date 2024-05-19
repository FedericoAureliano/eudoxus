class Sequential(Module):
    def locals(self):
        self.x = int
    
    def next(self):
        if self.x == 0:
            self.x = self.x + 1
        self.x = self.x - 1