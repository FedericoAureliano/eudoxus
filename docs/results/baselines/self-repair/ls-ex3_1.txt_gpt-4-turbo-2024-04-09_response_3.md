```uclid
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