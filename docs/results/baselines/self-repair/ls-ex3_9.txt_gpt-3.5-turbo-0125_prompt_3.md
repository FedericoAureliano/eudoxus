
Fix the following UCLID5 code using the compiler feedback provided below.

```

-- Declare variables
var count : int = 0;
var pedestrian : bool = false;
var sigG : bool = false;
var sigY : bool = false;
var sigR : bool = true;

-- Define state machine
state_machine traffic_light {
    state red {
        count := count + 1;
        if(count = 60){
            next_state := green;
            sigR := false;
            sigG := true;
            count := 0;
        } else {
            next_state := red;
        }
    }
    
    state green {
        if(pedestrian){
            next_state := yellow;
            sigG := false;
            sigY := true;
            count := 0;
        } else if(count = 60){
            next_state := pending;
            count := 0;
        } else {
            next_state := green;
        }
    }
    
    state yellow {
        count := count + 1;
        if(count = 5){
            next_state := red;
            sigY := false;
            sigR := true;
            count := 0;
        } else {
            next_state := yellow;
        }
    }
    
    state pending {
        if(count = (60-5)){
            next_state := yellow;
            count := 0;
        } else {
            next_state := pending;
            count := count + 1;
        }
    }
}

-- Initial state
initial red;

-- Transitions for pedestrian input
transition when pedestrian = true {
    pedestrian := true;
}

-- Clock tick every second
transition {
    count := count + 1;
}
```

Compiler feedback:

```
Syntax error on tmp.ucl, line 2: end of input expected.
-- Declare variables

```
Reply with your UCLID5 code inside one unique code block.

I can definitely do that! Here is the UCLID5 code:
```
