
Fix the following UCLID5 code using the compiler feedback provided below.

```

module ParkingCounter {
  // State variables
  var counter : integer; 

  // Define the initial state of the counter 
  init(counter) {
    counter = 0;
  }

  // Actions
  input arrival;
  input departure;

  // Update counter based on events
  next(counter) {
    if (arrival) {
      counter' = counter + 1;
    } else if (departure) {
      counter' = (counter > 0) ? counter - 1 : 0; // Ensure the counter does not go below zero
    } else {
      counter' = counter; // No change if no event
    }
  }
  
  // Control block
  control {
    var display : integer;
    init(display) {
      display = 0;
    }
    
    // Monitor and update the display whenever counter updates
    always {
      if (counter' != counter) {
        display = counter';
      }
    }
  }
  
  // Outputs 
  output display;
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
Syntax error on line 7: Syntax Error after keyword init.
  init(counter) {

```
Reply with your UCLID5 code inside one unique code block.

I can definitely do that! Here is the UCLID5 code:
```
