```uclid5
module main {
    type state_t;
    const red : state_t;
    const green : state_t;
    const yellow : state_t;
    const pending : state_t;

    input pedestrian : boolean;
    var sigG : boolean;
    var sigY : boolean;
    var sigR : boolean;
    var count : integer;
    var current_state : state_t;

    init {
        count = 0;
        current_state = red;
        sigG = false;
        sigY = false;
        sigR = true;
    }

    next {
        if (current_state == red) {
            if (count == 60) {
                current_state' = green;
                count' = 0;
                sigG' = true;
                sigY' = false;
                sigR' = false;
            } else {
                count' = count + 1;
            }
        } else if (current_state == green) {
            if (pedestrian) {
                if (count >= 60) {
                    current_state' = yellow;
                    count' = 0;
                    sigG' = false;
                    sigY' = true;
                    sigR' = false;
                } else {
                    count' = count + 1;
                }
            } else {
                if (count >= 60) {
                    current_state' = yellow;
                    count' = 0;
                    sigG' = false;
                    sigY' = true;
                    sigR' = false;
                } else {
                    count' = count + 1;
                }
            }
        } else if (current_state == pending) {
            if (count == 60) {
                current_state' = yellow;
                count' = 0;
                sigG' = false;
                sigY' = true;
                sigR' = false;
            } else {
                count' = count + 1;
            }
        } else if (current_state == yellow) {
            if (count == 5) {
                current_state' = red;
                count' = 0;
                sigG' = false;
                sigY' = false;
                sigR' = true;
            } else {
                count' = count + 1;
            }
        }
    }
}
```