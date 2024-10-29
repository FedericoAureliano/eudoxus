```
module main {
  type state_t = enum { RED, GREEN, YELLOW, PENDING };
  
  // State variables
  var currentState : state_t;
  var count : int;
  
  // Inputs
  input pedestrian : boolean;

  // Outputs
  var sigR : boolean;
  var sigY : boolean;
  var sigG : boolean;

  // Initialization
  init {
    currentState = RED;
    count = 0;
    sigR = true;
    sigY = false;
    sigG = false;
  }

  // Transition function
  next {
    // Default action to hold previous state values unless updated
    currentState' = currentState;
    count' = count + 1;
    
    // Update state only based on conditions
    if (currentState == RED) {
      if (count >= 60) {
        currentState' = GREEN;
        count' = 0;
      }
    } else if (currentState == GREEN) {
      if (pedestrian && count < 60) {
        currentState' = PENDING;
      } else if (!pedestrian && count >= 60) {
        currentState' = YELLOW;
        count' = 0;
      }
    } else if (currentState == PENDING) {
      if (count >= 60) {
        currentState' = YELLOW;
        count' = 0;
      }
    } else if (currentState == YELLOW) {
      if (count >= 5) {
        currentState' = RED;
        count' = 0;
      }
    }

    // Managing output signals according to the new state.
    if (currentState' == RED) {
      sigR' = true;
      sigY' = false;
      sigG' = false;
    } else if (currentState' == GREEN || currentState' == PENDING) {
      sigR' = false;
      sigY' = false;
      sigG' = true;
    } else if (currentState' == YELLOW) {
      sigR' = false;
      sigY' = true;
      sigG' = false;
    }
  }

  // Safety properties
  invariant maintainGreenMinimumTime {
    currentState == GREEN && count < 60 -> currentState' == PENDING
  }

  // Specification of the state machine behavior
  control {
    while(true) {
      delay(1); // assume one second passes each step
      havoc pedestrian;
      step;
    }
  }
}
```