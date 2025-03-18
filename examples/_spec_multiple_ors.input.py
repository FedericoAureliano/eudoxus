class Thermostat(Module):
    def types(self):
        self.temp = Real()

    def locals(self):
        self.heating = Boolean()
        self.cooling = Boolean()
        self.heatOn = Boolean()
        self.heatOff = Boolean()

    def inputs(self):
        pass

    def outputs(self):
        pass

    def init(self):
        self.heating = False
        self.cooling = False
        self.heatOn = False
        self.heatOff = False

    def next(self):
        # Activation Condition for Heating
        if self.temp > 22 and not self.heating and not self.cooling:
            self.heating = True
            self.cooling = False
            self.heatOn = True
            self.heatOff = False
        # Activation Condition for Cooling
        elif self.temp < 18 and not self.cooling and not self.heating:
            self.cooling = True
            self.heating = False
            self.heatOn = False
            self.heatOff = True
        # Refine the Heating and Cooling State Transitions
        elif self.temp <= 20 and self.heating:
            self.heating = False
            self.heatOn = False
        elif self.temp >= 20 and self.cooling:
            self.cooling = False
            self.heatOff = False

    def specification(self):
        return Or(
            Implies(self.heating, Not(self.cooling)),
            Implies(self.cooling, Not(self.heating)),
            Implies(self.heatOn, Not(self.heatOff)),
            Implies(self.heatOff, Not(self.heatOn)),
        )
