```uclid
// Define the module for the traffic light system
module traffic_light {
    // Enumerating traffic light states
    type state_t = enum { RED, GREEN, YELLOW };

    // State variable to denote the current state of traffic light
    var current_state : state_t;

    // State variable to keep track of previous state
    var previous_state : state_t;

    // Initialization
    init {
        // Started with RED and assuming YELLOW was before that
        current_state = RED;
        previous_state = YELLOW;
    }

    // Transition relation
    next {
        // Define the next state transition based on the current state
        match (current_state) {
            RED    : { previous_state' = current_state; current_state' = GREEN; }
            GREEN  : { previous_state' = current_state; current_state' = YELLOW; }
            YELLOW : { previous_state' = current_state; current_state' = RED; }
        }
    }

    // Safety property: every RED phase must be immediately preceded by YELLOW
    invariant red_follows_yellow {
        // Check if the current state is RED. If yes, check if the previous state was YELLOW
        if (current_state == RED) {
            previous_state == YELLOW
        } else {
            true // Other transitions do not violate the invariant
        }
    }
}
```

This UCLID5 code models a simple traffic light that cycles through red, green, and yellow. The `current_state` variable tracks the phase of the traffic light. The property being checked (`red_follows_yellow`) ensures that each red phase is immediately preceded by a yellow phase, using a previous state `previous_state` to remember the state before the current one. The transitions are simple and cyclic, from RED to GREEN, GREEN to YELLOW, and YELLOW back to RED.