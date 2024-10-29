```module main {
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
        temp = 18; // initialize temperature, for instance starting at 18 degrees
    }

    // Transition function
    next {
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