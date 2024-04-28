class Clock(Module):
  def outputs(self):
    self.tick = bool

  def next(self):
    self.tick = not self.tick

class TickCounter(Module):
  def locals(self):
    self.count = int

  def inputs(self):
    self.clock_tick = bool

  def instances(self):
    self.clock = Clock(tick=self.clock_tick)

  def init(self):
    self.count = 0

  def next(self):
    if self.clock_tick and self.count < 7:
      self.count = self.count + 1
    else:
      self.count = 0

  def specification(self):
    return self.count >= 0 and self.count <= 7

class System(Module):
  def instances(self):
    self.tick_counter = TickCounter()

  def control(self):
    self.induction(1)

