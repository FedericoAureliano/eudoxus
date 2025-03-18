"""def specification(self):
    always = And(
        ForAll(, Or(
            self.State == 'Purple',
            self.State == 'Orange',
            self.State == 'Blue'
        )),
        ForAll(, Implies(
            self.State == 'Purple',
            Exists(, And(
                self.State(self.t1) == 'Orange',
                self.time > self.t1
            ))
        )),
        ForAll(, Implies(
            self.State == 'Orange',
            Exists(, And(
                self.State(self.t2) == 'Blue',
                self.time > self.t2
            ))
        )),
        ForAll(, Implies(
            self.State == 'Blue',
            Exists(, And(
                self.State(self.t3) == 'Purple',
                self.time > self.t3
            ))
        )),
        ForAll(, Not(self.State == Next(self.time, self.State)))
    )
    return always
"""
