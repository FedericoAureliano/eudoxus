
Fix the following UCLID5 code using the compiler feedback provided below.

```

module main {
  // Define states for the traffic lights
  type state_t = enum { RED, GREEN, YELLOW };
  type main_light_t = enum { GREEN_PHASE, YELLOW_PHASE, RED_PHASE };
  type secondary_light_t = enum { RED_WAIT, GREEN_PHASE, YELLOW_PHASE };

  // Variables representing the state of each of the lights on both roads
  var ml : main_light_t;
  var sl : secondary_light_t;
  var timer : int;
  var vehicle_detected : boolean;

  // Constants for timing
  const lengthMainGreen : int = 180;    // Main green phase: 3 minutes (180 seconds)
  const lengthMainYellow : int = 5;     // Main yellow phase: 5 seconds
  const lengthMainRed : int = 55;       // Main red phase: 55 seconds
  const lengthSecGreen : int = 50;      // Secondary green phase: 50 seconds
  const lengthSecYellow : int = 5;      // Secondary yellow phase: 5 seconds

  init {
    ml = GREEN_PHASE;
    sl = RED_WAIT;
    timer = 0;
    vehicle_detected = false;
  }

  // Update timer
  next(timer) {
    if (timer < lengthMainGreen + lengthMainYellow + lengthMainRed)
      return timer + 1;
    else
      return 0;
  }

  // Update vehicle detection input
  input (vehicle_detected_signal: boolean);
  next(vehicle_detected) {
    return vehicle_detected_signal;
  }
  
  // Update main light state
  next(ml) {
    switch (ml) {
      case GREEN_PHASE:
        if (timer >= lengthMainGreen)
          return YELLOW_PHASE;
        else 
          return GREEN_PHASE;
      case YELLOW_PHASE:
        if (timer >= lengthMainGreen + lengthMainYellow)
          return RED_PHASE;
        else 
          return YELLOW_PHASE;
      case RED_PHASE:
        if (timer >= lengthMainGreen + lengthMainYellow + lengthMainRed)
          return GREEN_PHASE;
        else 
          return RED_PHASE;
      default: 
        return ml;
    }
  }

  // Update secondary light state
  next(sl) {
    switch (sl) {
      case RED_WAIT:
        if (timer >= lengthMainGreen + lengthMainYellow)
          return GREEN_PHASE;
        else 
          return RED_WAIT;
      case GREEN_PHASE:
        if (timer >= lengthMainGreen + lengthMainYellow + lengthSecGreen)
          return YELLOW_PHASE;
        else 
          return GREEN_PHASE;
      case YELLOW_PHASE:
        if (timer >= lengthMainGreen + lengthMainYellow + lengthSecGreen + lengthSecYellow)
          return RED_WAIT;
        else 
          return YELLOW_PHASE;
      default: 
        return sl;
    }
  }

  // Output functions for light signaling
  define mG = (ml == GREEN_PHASE);
  define mY = (ml == YELLOW_PHASE);
  define mR = (ml == RED_PHASE);
  define sG = (sl == GREEN_PHASE);
  define sY = (sl == YELLOW_PHASE);
  define sR = (sl == RED_WAIT);
}
```

Compiler feedback:

```
Syntax error on line 29: Syntax Error after keyword next.
  next(timer) {

```
Reply with your UCLID5 code inside one unique code block.

I can definitely do that! Here is the UCLID5 code:
```
