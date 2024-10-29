```
module main {
    type real_t = real;

    // Constants for the setpoint temperatures
    const setpoint : real_t = 20.0;
    const upperLimit : real_t = 22.0;
    const lowerLimit : real_t = 18.0;

    // Input representing the current temperature
    input temp : real_t;

    // State variable indicating if the heater is on
    var heaterOn : boolean;

    // Outputs to indicate if the heater needs to turn on or off
    define heatOn : boolean = (heaterOn == false && temp <= lowerLimit);
    define heatOff : boolean = (heaterOn == true && temp >= upperLimit);

    // Initial state
    init {
        // Assume heater starts off
        heaterOn = false;
    }

    // Transition relation
    next(heaterOn) {
        if (heatOn) {
            return true;    
        } else if (heatOff) {
            return false;
        } else {
            return heaterOn;
        }    
    }

    // Rules for safety check
    invariant heatControl {
        // Here, rules to enforce correct behavior of the heater at all times
        // Rule 1: Heater must be turned on when below lowerLimit
        (temp <= lowerLimit -> heaterOn == true) &&
        // Rule 2: Heater must be turned off when above upperLimit
        (temp >= upperLimit -> heaterOn == false);
    }
}
```