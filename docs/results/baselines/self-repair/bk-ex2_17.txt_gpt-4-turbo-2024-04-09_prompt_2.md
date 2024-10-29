
Fix the following UCLID5 code using the compiler feedback provided below.

```

module main {
  type state_t = { RED, GREEN };

  var current_state : state_t;

  init {
    current_state = RED;
  }

  next {
    current_state = 
      match (current_state) {
        RED   : GREEN,
        GREEN : RED
      };
  }

  // Safety property to check: The light should not be RED and GREEN at the same time.
  property mutual_exclusion {
    current_state = RED -> !(current_state = GREEN);
  }

  // LED visual representation of the traffic light
  // This is just for readability of output, not part of the actual logic
  control {
    if (current_state == RED) { print "Red Light" ; }
    else if (current_state == GREEN) { print "Green Light" ; }
  }
}
```

Compiler feedback:

```
Syntax error on line 13: Syntax Error in Expression.
      match (current_state) {

```
Reply with your UCLID5 code inside one unique code block.

I can definitely do that! Here is the UCLID5 code:
```
