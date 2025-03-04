```uclid
// Define a module
module vending_machine {
    // Variables definition
    var coin : integer;
    var dispensed_drinks : integer;

    // Initialization
    init {
        coin = 0;
        dispensed_drinks = 0;
    }

    // Transition relation for coin
    next(coin) {
        coin := 
          case
              coin < 10 : coin + 1; // Maximum coins allowed is 10
              true : coin;
          esac;
    }

    // Transition relation for dispensed_drinks
    next(dispensed_drinks) {
        dispensed_drinks := 
          case
              coin > dispensed_drinks : dispensed_drinks + 1; // Dispense drink only if there are enough coins
              true : dispensed_drinks;
          esac;
    }

    // Safety property
    // Ensure the number of inserted coins is always at least the number of dispensed drinks
    invariant safety_property {
        coin >= dispensed_drinks
    }
}
```