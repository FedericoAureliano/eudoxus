```
module main {
    type state_t;
    const red   : state_t;
    const green : state_t;

    var light1 : state_t; // State of the first traffic light
    var light2 : state_t; // State of the second traffic light
    
    init {
        light1 = red;
        light2 = red;
    }
    
    next {
        light1 := 
            case 
                light1 = red   : green;
                light1 = green : red;
                true           : light1;
            esac;

        light2 := 
            case 
                light2 = red   : green;
                light2 = green : red;
                true           : light2;
            esac;
    }
    
    invariant "safe_traffic" : !(light1 = green && light2 = green);
}
```