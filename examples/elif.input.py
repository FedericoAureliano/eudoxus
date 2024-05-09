class Elif(Module):
    def locals (self):
        self.x = real()
        self.y = real()

    def next (self):
        if self.x == 0:
            self.y = 0
        elif self.x == 1:
            self.y = 1
        elif self.x == 2:
            self.y = -2
        else:
            self.y = 0.5
    