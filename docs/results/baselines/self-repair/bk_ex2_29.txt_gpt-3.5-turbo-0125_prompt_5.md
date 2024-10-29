
Fix the following UCLID5 code using the compiler feedback provided below.

```

(state : type)

(variables
    BCR_state : state;
    BP_state : state;
    Printer_state : state;)

(constants)

(axioms)

(rules
    BCR_state = 0 | BCR_state = 1;
    BP_state = 0 | BP_state = 1;
    Printer_state = 0 | Printer_state = 1;)

(init
    BCR_state = 0;
    BP_state = 0;
    Printer_state = 0;)

(transitions
    BCR_state' = 1 & BCR_state = 0 & BP_state' = 1;
    BP_state' = 0 & BP_state = 1 & Printer_state' = 1;
    Printer_state' = 0 & Printer_state = 1;)
```

Compiler feedback:

```
Syntax error on tmp.ucl, line 2: end of input expected.
(state : type)

```
Reply with your UCLID5 code inside one unique code block.

I can definitely do that! Here is the UCLID5 code:
```
