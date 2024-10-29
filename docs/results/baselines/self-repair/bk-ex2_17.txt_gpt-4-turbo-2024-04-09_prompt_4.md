
Fix the following UCLID5 code using the compiler feedback provided below.

```

  type state_t = enum { RED, GREEN };

  var current_state : state_t;

  init {
    current_state = RED;
  }

  next {
    current_state = 
      if (current_state == RED) then GREEN
      else RED;
  }

  // Safety property to check: The light should not be RED and GREEN at the same time.
  property mutual_exclusion {
    !(current_state == RED && current_state == GREEN);
  }

  control {
    if (current_state == RED) { print "Red Light"; }
    else if (current_state == GREEN) { print "Green Light"; }
  }
}
```

Compiler feedback:

```
Syntax error on tmp.ucl, line 2: end of input expected.
  type state_t = enum { RED, GREEN };

```
Reply with your UCLID5 code inside one unique code block.

I can definitely do that! Here is the UCLID5 code:
```
