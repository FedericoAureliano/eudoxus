class Keywords:
    def types(self):
        self.integer = int
    
    def outputs(self):
        self.x = self.integer()
    
    def spec(self):
        return self.x == 5