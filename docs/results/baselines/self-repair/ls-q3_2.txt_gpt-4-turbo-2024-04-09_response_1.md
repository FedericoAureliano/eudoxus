```uclid
module main {
    type Timer;
    type Temperature;

    // Define constants for time durations
    const min_off : Timer = 4; // 2 minutes off (4 * 30 seconds)
    const min_on : Timer = 1; // 30 seconds on

    // Variables
    var temp : Temperature;
    var heatOn : boolean;
    var heatOff : boolean;
    var timeSinceToggle : Timer;

    // Initialization
    init {
        heatOn = false;
        heatOff = true;
        timeSinceToggle = 0;
        // initialize temperature, for instance starting at 18 degrees
        temp = 18;
    }

    // Transition function
    next {
        // Rreact every 30 seconds, modeling this with time, which automatically increments
        timeSinceToggle = timeSinceToggle + 1;

        if (temp <= 20) {
            // If temperature is less or equal than 20 degrees Celsius 
            if (heatOff && timeSinceToggle >= min_on) {
                heatOn = true;
                heatOff = false;
                timeSinceToggle = 0;
            }
        } else if (temp > 20) {
            // If temperature is greater than 20 degrees Celsius
            if (heatOn && timeSinceToggle >= min_off) {
                heatOn = false;
                heatOff = true;
                timeSinceToggle = 0;
            }
        }
    }

    // Safety property: the heater should not toggle states more quickly than specified
    invariant "heater_min_on" {
        (heatOn && timeSinceToggle < min_on) -> (heatOn' && !heatOff')
    }

    invariant "heater_min_off" {
        (heatOff && timeSinceToggle < min_off) -> (heatOff' && !heatOn')
    }
}
```

This UCLID5 code models a thermostat controlling a heating system as described, with careful handling of on/off state transitions based on temperature and time elapsed since the last transition. The model transitions states only once every 30 seconds, in accordance with the given time increments and conditions for changing states. The invariants ensure that the minimum duration conditions for the heater being on and off are satisfied.