(state : type)

(variables
    BCR_state : state
    BP_state : state
    Printer_state : state)

(constants)

(axioms)

(rules
    BCR_state = 0 | BCR_state = 1
    BP_state = 0 | BP_state = 1
    Printer_state = 0 | Printer_state = 1)

(init
    BCR_state = 0
    BP_state = 0
    Printer_state = 0)

(transitions
    BCR_state' = 1 & BCR_state = 0 & BP_state' = 1
    BP_state' = 0 & BP_state = 1 & Printer_state' = 1
    Printer_state' = 0 & Printer_state = 1)
```