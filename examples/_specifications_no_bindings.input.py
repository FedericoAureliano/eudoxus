class ParkingGarage(Module):
    def types(self):
        self.arrival = Boolean()
        self.departure = Boolean()
        self.counter = Integer()

    def locals(self):
        self.display = String()

    def inputs(self):
        self.arrival_detector = ArrivalDetector()
        self.departure_detector = DepartureDetector()

    def outputs(self):
        self.display_output = DisplayOutput()

    def instances(self):
        self.counter = Counter(i=0)

    def next(self):
        if self.arrival == True:
            self.counter = 1

    def specification(self):
        return self.display_output.text == self.display
