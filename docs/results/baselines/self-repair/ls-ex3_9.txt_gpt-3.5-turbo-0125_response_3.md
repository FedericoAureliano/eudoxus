```uclid
-- Declare variables
var count : int = 0;
var pedestrian : bool = false;
var sigG : bool = false;
var sigY : bool = false;
var sigR : bool = true;

-- Define state machine
state traffic_light {
    red {
        count := count + 1;
        if(count = 60){
            next(red) := green;
            sigR := false;
            sigG := true;
            count := 0;
        } else {
            next(red) := red;
        }
    }
    
    green {
        if(pedestrian){
            next(green) := yellow;
            sigG := false;
            sigY := true;
            count := 0;
        } else if(count = 60){
            next(green) := pending;
            count := 0;
        } else {
            next(green) := green;
        }
    }
    
    yellow {
        count := count + 1;
        if(count = 5){
            next(yellow) := red;
            sigY := false;
            sigR := true;
            count := 0;
        } else {
            next(yellow) := yellow;
        }
    }
    
    pending {
        if(count = (60-5)){
            next(pending) := yellow;
            count := 0;
        } else {
            next(pending) := pending;
            count := count + 1;
        }
    }
}

-- Initial state
initial traffic_light.red;

-- Transitions for pedestrian input
transition when pedestrian = true {
    pedestrian := true;
}

-- Clock tick every second
transition {
    count := count + 1;
}
```