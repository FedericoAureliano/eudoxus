
Fix the following UCLID5 code using the compiler feedback provided below.

```

// Model for three concurrent processes operating on a shared variable x.
module concurrent_processes {
    // Declare the shared integer variable x with arbitrary initial value
    var x : int;

    // The init block should assign an initial value to x
    init {
        x := *;     // non-deterministic initial value
        assume (x >= 0 && x <= 200);
    }

    // Processes definitions

    // Process Inc: increments x if x < 200
    procedure Inc() {
        while (true) {
            if (x < 200) {
                x := x + 1;
            }
        }
    }

    // Process Dec: decrements x if x > 0
    procedure Dec() {
        while (true) {
            if (x > 0) {
                x := x - 1;
            }
        }
    }

    // Process Reset: resets x to 0 if x == 200
    procedure Reset() {
        while (true) {
            if (x == 200) {
                x := 0;
            }
        }
    }

    // Main process that starts all the other processes concurrently
    procedure main() {
        fork {
            call Inc();
            call Dec();
            call Reset();
        }
    }

    // Define invariant to ensure x is always between 0 and 200
    invariant x >= 0 && x <= 200; // Use '&&' for logical AND

    // Specify next state relation using havoc to model non-determinism of concurrent execution
    next {
        havoc x;
        assume (x >= 0 && x <= 200); // maintaining the invariant constraint and use '&&' for logical AND
    }

    // Safety properties to check
    control {
        check;
    }
}
```

Compiler feedback:

```
Syntax error on line 9: Syntax Error in Expression.
        x := *;     // non-deterministic initial value

```
Reply with your UCLID5 code inside one unique code block.

I can definitely do that! Here is the UCLID5 code:
```
