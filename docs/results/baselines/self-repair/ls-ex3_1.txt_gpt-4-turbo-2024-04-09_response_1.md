```uclid
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
This UCLID5 code models a parking counter where the counter is initialized at zero and updated based on the arrivals and departures detected. The control block ensures that any change in the counter is immediately reflected on a display.