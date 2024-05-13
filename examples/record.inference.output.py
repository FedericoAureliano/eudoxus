class Record(Module):
    def types(self):
        self.triple = Record(('x', Real()), ('y', Real()), ('z', Real()))

    def locals(self):
        self.p = self.triple

    def init(self):
        assert self.p.x == 0.0
        assert ?? == 0