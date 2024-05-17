class With(Module):
    def locals(self):
        self.x = int
    
    def main(self):
        with self.x as x:
            x = 1