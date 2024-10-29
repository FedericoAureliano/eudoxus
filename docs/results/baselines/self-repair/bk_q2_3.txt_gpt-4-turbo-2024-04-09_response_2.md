```uclid
module traffic_light_system {
    type light_state_t;
    const green : light_state_t;
    const yellow : light_state_t;
    const red : light_state_t;
    const amber : light_state_t;
    
    var L1, L2, L3, L4 : light_state_t;

    init {
        L1 = red;
        L2 = red;
        L3 = red;
        L4 = red;
    }

    procedure next_light_state(current : light_state_t) returns (next_state : light_state_t) {
        if (current == green) {
            next_state = yellow;
        } else if (current == yellow) {
            next_state = red;
        } else if (current == red) {
            next_state = amber;
        } else if (current == amber) {
            next_state = green;
        }
    } // End of next_light_state procedure

    next {
        L1 = (L1 == red && L3 != red) ? amber : next_light_state(L1);
        L2 = (L2 == red && L1 == red && L3 == red) ? amber : next_light_state(L2);
        L3 = (L3 == red && L1 != red) ? amber : next_light_state(L3);
        L4 = (L4 == red && L2 == red) ? amber : next_light_state(L4);
    }

    control {
        ensure (L1 == green && L3 == green) || (L2 == green) || (L4 == green);
        ensure (L1 != green || L2 != green);
        ensure (L3 != green || L4 != green);
        ensure (L2 != green || L4 != green);
        ensure (L1 != green || L3 != green);
    }
}
```
This code corrects the bracket usage, ensuring that each procedure block, including `next_light_state`, is correctly closed. The proper syntax for control clauses is used, where multiple conditions are separated by semicolons. The use of question marks and colons in conditional (ternary) assignments is syntactically correct, matching the patterns often seen in many programming languages.