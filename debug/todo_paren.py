"""class MarsTrafficLight(Module):
    def types(self):
        self.TrafficLight = int

    def locals(self):
        self.state = self.TrafficLight

    def init(self):
        self.state = 2

    def next(self):
        if self.state == 0:
            self.state = 1
        else:
            if self.state == 1:
                self.state = 2
            else:
                self.state = 0

    def specification(self):
        return True
"""
