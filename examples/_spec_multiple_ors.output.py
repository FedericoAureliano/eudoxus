class Thermostat(Module):
    def locals(self):
        self.temp = int
        self.heating = bool
        self.cooling = bool
        self.heatOn = bool
        self.heatOff = bool

    def init(self):
        self.heating = False
        self.cooling = False
        self.heatOn = False
        self.heatOff = False

    def next(self):
        if ((self.temp > 22) and not self.heating) and not self.cooling:
            self.heating = True
            self.cooling = False
            self.heatOn = True
            self.heatOff = False
        else:
            if ((self.temp < 18) and not self.cooling) and not self.heating:
                self.cooling = True
                self.heating = False
                self.heatOn = False
                self.heatOff = True
            else:
                if (self.temp <= 20) and self.heating:
                    self.heating = False
                    self.heatOn = False
                else:
                    if (self.temp >= 20) and self.cooling:
                        self.cooling = False
                        self.heatOff = False

    def specification(self):
        return Implies(self.heatOff, not self.heatOn) or (
            Implies(self.heatOn, not self.heatOff)
            or (
                Implies(self.heating, not self.cooling)
                or Implies(self.cooling, not self.heating)
            )
        )
