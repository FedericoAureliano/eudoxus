
Fix the following UCLID5 code using the compiler feedback provided below.

```

module main {
    type real = real;

    // Constants for the setpoint temperatures
    const setpoint : real = 20.0;
    const upperLimit : real = 22.0;
    const lowerLimit : real = 18.0;

    // Input representing the current temperature
    input temp : real;

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
    invariant heatControl : boolean {
        // Here, rules to enforce correct behavior of the heater at all times
        // Rule 1: Heater must be turned on when below lowerLimit
        (temp <= lowerLimit -> heaterOn == true) and
        // Rule 2: Heater must be turned off when above upperLimit
        (temp >= upperLimit -> heaterOn == false);
    }
}
```

Compiler feedback:

```
Syntax error on line 3: Syntax Error after keyword type.
    type real = real;

```
Reply with your UCLID5 code inside one unique code block.

I can definitely do that! Here is the UCLID5 code:
```
