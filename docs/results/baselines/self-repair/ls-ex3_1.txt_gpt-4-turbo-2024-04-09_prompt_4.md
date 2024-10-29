
Fix the following UCLID5 code using the compiler feedback provided below.

```

module ParkingCounter {
  // State variables
  var counter : integer; 

  // Define the initial state of the counter 
  init {
    counter = 0;
  }

  // Inputs
  input arrival : boolean;
  input departure : boolean;

  // Update counter based on events
  next {
    if (arrival) {
      counter' = counter + 1;
    } else if (departure) {
      counter' = counter > 0 ? counter - 1 : 0; // Ensure the counter does not go below zero
    } else {
      counter' = counter; // No change if no event
    }
  }
  
  // Output
  output display : integer;
  init {
    display = 0;
  }

  // Control block to update the display
  next {
    display = counter';
  }
}

// Example instantiation of the module
instance parkingGarage : ParkingCounter;

// Control program runs indefinitely, could be triggered by sensor inputs in a real-world application
control {
  loop {
    step;
  }
}
```

Compiler feedback:

```
Syntax error on line 16: unpaired '{' .
  next {

```
Reply with your UCLID5 code inside one unique code block.

I can definitely do that! Here is the UCLID5 code:
```
