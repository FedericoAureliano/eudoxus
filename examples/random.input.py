class Random(Module):
    def locals(self):
        self.x = int
        self.y = bool

    def init(self):
        self.x = random.random()
        self.y = choice([True])

        if random() < 0.5:
            self.x = 1

        if random():
            self.y = False