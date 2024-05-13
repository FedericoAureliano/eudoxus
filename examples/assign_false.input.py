class AssignFalse(Module):
    def locals(self):
        self.x = bool
        self.y = bool

    def init(self):
        self.x = False
        self.y = True