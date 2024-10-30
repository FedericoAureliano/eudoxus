```
; Declare the types
(state : type)

; Declare the variables
(variables
    BCR_state : state;
    BP_state : state;
    Printer_state : state;)

; Declare the constants
(constants)

; Declare the axioms
(axioms)

; Define the rules
(rules
    BCR_state = 0 | BCR_state = 1;
    BP_state = 0 | BP_state = 1;
    Printer_state = 0 | Printer_state = 1;)

; Initialize the variables
(init
    BCR_state = 0;
    BP_state = 0;
    Printer_state = 0;)

; Define the transitions
(transitions
    BCR_state' = 1 & BCR_state = 0 & BP_state' = 1;
    BP_state' = 0 & BP_state = 1 & Printer_state' = 1;
    Printer_state' = 0 & Printer_state = 1;)
```