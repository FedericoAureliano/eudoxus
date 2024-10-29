```uclid
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
    
    // Transition relation for when the first light switches state
    next(light1) := 
        case 
            light1 = red   -> green;
            light1 = green -> red;
            true           -> light1;
        esac;

    // Transition relation for when the second light switches state
    next(light2) := 
        case 
            light2 = red   -> green;
            light2 = green -> red;
            true           -> light2;
        esac;
    
    // Safety property: Avoid both lights being green simultaneously
    invariant "safe_traffic" : !(light1 = green && light2 = green);
}

```
This UCLID5 code represents two independent traffic lights modeled as a transition system. Each light can be either in a 'green' state or a 'red' state. The transitions in the model permit each light to switch from red to green or from green back to red. Despite their independence, a safety invariant ensures that not both lights are green at the same time to prevent crossing traffic conflicts, although the roads are parallel and non-intersecting as per the problem description.