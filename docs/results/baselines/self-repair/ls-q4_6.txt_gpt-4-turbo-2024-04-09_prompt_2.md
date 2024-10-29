
Fix the following UCLID5 code using the compiler feedback provided below.

```

module main {
    type time_t;
    var light_on : boolean;
    var door_open : boolean;
    var time : time_t;

    init {
        light_on = false;
        door_open = false;
        time = 0;
    }

    next(door_open_prime : boolean) {
        if (door_open || door_open_prime) {     // A door is opened
            light_on' = true;
            time' = 0;
        } else if (time >= 30) {                // 30 seconds after all doors are closed
            light_on' = false;
        } else {                                // Counting 30 seconds while all doors are closed
            light_on' = light_on;
            time' = time + 1;
        }
    }

    // Safety property: light should be on any time a door is open
    property light_on_when_door_open {
        door_open -> light_on;
    }

    // Safety property: light should turn off only 30 seconds after all doors are closed
    property light_off_after_delay {
        (time >= 30) && !door_open -> !light_on;
    }
}
```

Compiler feedback:

```
Syntax error on line 14: Syntax Error after keyword next.
    next(door_open_prime : boolean) {

```
Reply with your UCLID5 code inside one unique code block.

I can definitely do that! Here is the UCLID5 code:
```
