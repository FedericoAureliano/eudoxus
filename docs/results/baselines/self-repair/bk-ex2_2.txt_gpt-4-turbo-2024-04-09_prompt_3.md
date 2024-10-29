
Fix the following UCLID5 code using the compiler feedback provided below.

```

    type state_t;
    const pay : state_t;
    const select : state_t;
    const soda : state_t;
    const beer : state_t;

    var curr_state : state_t;
    var coin_inserted : boolean;

    init {
        curr_state = pay;
        coin_inserted = false;
    }

    transition {
        // Inserting a coin and moving from pay to select
        insert_coin : 
            curr_state = pay & !coin_inserted -> { 
                curr_state' = select; 
                coin_inserted' = true;
            }

        // Selecting soda and delivering it if coin was inserted
        get_soda : 
            curr_state = select & coin_inserted -> {
                curr_state' = soda;
                // Reset to initial state after delivery
                coin_inserted' = false;
            }

        // Selecting beer and delivering it if coin was inserted
        get_beer : 
            curr_state = select & coin_inserted -> {
                curr_state' = beer; 
                // Reset to initial state after delivery
                coin_inserted' = false;
            }
    }

    // The main property to check the machine only delivers a drink after coin insertion
    // and from state select exclusively
    property drink_delivery_after_payment = []( (curr_state = soda | curr_state = beer) -> last(coin_inserted) );

    control {
        check;
        simulate;
    }
}
```

Compiler feedback:

```
Syntax error on tmp.ucl, line 2: end of input expected.
    type state_t;

```
Reply with your UCLID5 code inside one unique code block.

I can definitely do that! Here is the UCLID5 code:
```
