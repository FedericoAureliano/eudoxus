
Fix the following UCLID5 code using the compiler feedback provided below.

```

  type state_t;
  const far : state_t;
  const near : state_t;
  const in : state_t;

  type gate_state_t;
  const up : gate_state_t;
  const down : gate_state_t;

  type controller_state_t;
  const state_0 : controller_state_t;
  const state_1 : controller_state_t;
  const state_2 : controller_state_t;
  const state_3 : controller_state_t;

  var train_state : state_t;
  var gate_state : gate_state_t;
  var controller_state : controller_state_t;

  init {
    train_state = far;
    gate_state = up;
    controller_state = state_0;
  }
  
  transition {
    train_state' = 
      switch (train_state) {
        case far : { choose(near, far) };
        case near : { in };
        case in : { far };
      };

    gate_state' = 
      switch (controller_state) {
        case state_0 : up;
        case state_1 : down;
        case state_2 : down;
        case state_3 : up;
      };

    controller_state' = 
      switch (controller_state) {
        case state_0 : { if (train_state == near) then state_1 else state_0 };
        case state_1 : { if (gate_state == down) then state_2 else state_1 };
        case state_2 : { if (train_state == far) then state_3 else state_2 };
        case state_3 : { if (gate_state == up) then state_0 else state_3 };
      };
  }

  // Safety property: When a train is in the "in" state, the gate must be "down".
  property safety_property {
    train_state == in -> gate_state == down;
  }
  
  // Valid initial state check.
  control {
    check;
    print_results;
  }

  invariant safety {
    train_state == in -> gate_state == down;
  }
}
```

Compiler feedback:

```
Syntax error on tmp.ucl, line 2: end of input expected.
  type state_t;

```
Reply with your UCLID5 code inside one unique code block.

I can definitely do that! Here is the UCLID5 code:
```
