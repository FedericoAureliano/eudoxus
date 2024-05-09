class Elif(Module):
    def locals (self):
        self.x = Real()
        self.y = Real()

    def next (self):
        if self.x == 0.0:
            self.y = 0.0
        else:
            if self.x == 1.0:
                self.y = 1.0
            else:
                if self.x == 2.0:
                    self.y = -2.0
                else:
                    self.y = 0.5
    