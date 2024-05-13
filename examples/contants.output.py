class Constants(Module):
    def specification(self):
        return 1 + 2 + 3 == 6 or True and False or BitVectorVal(2, 32) + BitVectorVal(2, 32) == BitVectorVal(4, 32) and 1.0 == 1.7777