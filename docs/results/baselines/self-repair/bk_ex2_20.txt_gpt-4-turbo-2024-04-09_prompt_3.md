
Fix the following UCLID5 code using the compiler feedback provided below.

```

module main {
    var x : int;
    type action_t = enum {IDLE, ACTION_A, ACTION_B};
    var action : action_t;

    init {
        x = 3;
        action = IDLE; // It's important to initialize 'action' in init
    }

    next(action) {
        action' = nondet(action_t); // Deterministic assignment
    }

    next {
        case
        action == ACTION_A: x' = 2 * x;
        action == ACTION_B: x' = x + 1;
        action == IDLE: x' = x;
        esac;
    }

    control {
        while (*) {
            if (*) {
                action = ACTION_A;
            } else {
                action = ACTION_B;
            }
        }
    }
}
```

Compiler feedback:

```
Syntax error on line 12: Syntax Error after keyword next.
    next(action) {

```
Reply with your UCLID5 code inside one unique code block.

I can definitely do that! Here is the UCLID5 code:
```
