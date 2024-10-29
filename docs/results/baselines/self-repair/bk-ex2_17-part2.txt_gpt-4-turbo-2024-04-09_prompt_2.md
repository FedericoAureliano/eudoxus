
Fix the following UCLID5 code using the compiler feedback provided below.

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

Compiler feedback:

```
Syntax error on line 16: Syntax Error after keyword next.
    next(light1) := 

```
Reply with your UCLID5 code inside one unique code block.

I can definitely do that! Here is the UCLID5 code:
```
