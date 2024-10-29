```uclid
module main {
    type real;

    // Constant for the setpoint temperatures
    const setpoint : real = 20.0;
    const upperLimit : real = 22.0;
    const lowerLimit : real = 18.0;

    // Input representing the current temperature
    input temp : real;

    // State variable indicating if the heater is on
    var heaterOn : boolean;

    // Outputs to indicate if the heater needs to turn on or off
    synthesize heatOn : boolean = (heaterOn == false && temp <= lowerLimit);
    synthesize heatOff : boolean = (heaterOn == true && temp >= upperLimit);

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
        (temp <= lowerLimit -> heaterOn == true) and
        // Rule 2: Heater must be turned off when above upperLimit
        (temp >= upperLimit -> heaterOn == false);
    }
}
```
This UCLID5 model describes a simple thermostat with hysteresis. The temperature (`temp`) is checked against predefined thresholds, controlling when to command turning the heater on or off (`heatOn`, `heatOff`). The system transitions appropriately based on threshold readings, thereby maintaining an acceptable temperature range around a setpoint with hysteresis.