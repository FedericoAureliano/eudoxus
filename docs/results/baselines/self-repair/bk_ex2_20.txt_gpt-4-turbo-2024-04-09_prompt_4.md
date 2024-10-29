
Fix the following UCLID5 code using the compiler feedback provided below.

```

module main {
    var x : int;
    type action_t = enum {IDLE, ACTION_A, ACTION_B};
    var action : action_t;

    init {
        x = 3;
        action = IDLE; // It's important to initialize 'action' in init block
    }

    next {
        case
        is_nondeterministic_choice: 
            action' = nondet(action_t); // Corrected nondeterministic assignment to action
        else:
            case
            action == ACTION_A: x' = 2 * x;
            action == ACTION_B: x' = x + 1;
            action == IDLE: x' = x;
            esac;
        esac;
    }

    control {
        while (true) {
            if (nondet()) {
                havoc action;
            } 
        }
    }
}
```

Compiler feedback:

```
Syntax error on line 13: Syntax Error after keyword case.
        case

```
Reply with your UCLID5 code inside one unique code block.

I can definitely do that! Here is the UCLID5 code:
```
