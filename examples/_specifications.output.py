class Thermostat(Module):
    def locals(self):
        self.heatOff = bool
        self.heatOn = bool
        self.temp = int

    def init(self):
        self.temp = 20
        self.heatOn = True
        self.heatOff = False

    def next(self):
        if self.heatOn:
            if self.temp < 22:
                self.temp = self.temp + 10
            else:
                self.heatOn = False
                self.heatOff = True
        else:
            if self.heatOff:
                if self.temp > 18:
                    self.temp = self.temp - 1
                else:
                    self.heatOn = True
                    self.heatOff = False

    def specification(self):
        self.invariant1 = self.temp >= 20
        self.invariant2 = self.temp <= 22
        return self.invariant1 and self.invariant2
