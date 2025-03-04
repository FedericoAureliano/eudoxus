```
module main {
    type time_t = int;
    var light_on : boolean;
    var door_open : boolean;
    var time : time_t;

    init {
        light_on = false;
        door_open = false;
        time = 0;
    }

    input door_open' : boolean;

    next {
        light_on' = (door_open || door_open') || (light_on && !(time >= 30));
        time' = ite(door_open || door_open', 0, time + 1);
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