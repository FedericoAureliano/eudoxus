class Clock(Module):
    def outputs(self):
        self.tick = Bool()

    def next(self):
        self.tick = Not(self.tick)

class TickCounter(Module):
    def locals(self):
        self.count = BitVector(3)

    def inputs(self):
        self.clock_tick = Bool()

    def init(self):
        self.count = 0

    def next(self):
        if And(self.clock_tick, self.count < 7):
            self.count = self.count + 1
        else:
            self.count = 0

    def instances(self):
        self.clock = Clock(tick=self.clock_tick)

    def specification(self):
        return And(self.count >= 0, self.count <= 7)

class System(Module):
    def instances(self):
        self.tick_counter = TickCounter()

    def specification(self):
        return self.tick_counter.specification()

    def proof(self):
        induction(1)