
Fix the following UCLID5 code using the compiler feedback provided below.

```

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

Compiler feedback:

```
Syntax error on tmp.ucl, line 3: end of input expected.
    var coin : integer;

```
Reply with your UCLID5 code inside one unique code block.

I can definitely do that! Here is the UCLID5 code:
```