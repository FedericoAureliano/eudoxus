
Fix the following UCLID5 code using the compiler feedback provided below.

```

#lang uclid

var red : boolean;
var green : boolean;

-- initial state
init(red) := true;
init(green) := false;

-- transitions
next(red) :=
  case
    red : green;
    green : red;
  esac;

next(green) :=
  !red;

-- safety property: red and green cannot be true at the same time
system red_exclusive := ! (red && green);
```

Compiler feedback:

```
Syntax error on tmp.ucl, line 2: end of input expected.
#lang uclid

```
Reply with your UCLID5 code inside one unique code block.

I can definitely do that! Here is the UCLID5 code:
```
