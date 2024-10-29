
Fix the following UCLID5 code using the compiler feedback provided below.

```

module main {
    type state_t = enum { pay, select, soda, beer };

    var curr_state : state_t;
    var coin_inserted : boolean;

    init {
        curr_state = pay;
        coin_inserted = false;
    }

    transition {
        insert_coin:
            curr_state = pay & !coin_inserted -> {
                curr_state' = select; 
                coin_inserted' = true;
            }

        get_soda: 
            curr_state = select & coin_inserted -> {
                curr_state' = soda;
                coin_inserted' = false;
            }

        get_beer: 
            curr_state = select & coin_inserted -> {
                curr_state' = beer; 
                coin_inserted' = false;
            }
    }

    property drink_delivery_after_payment : []( (curr_state = soda | curr_state = beer) -> last(coin_inserted) );

    control {
        check;
        simulate;
    }
}
```

Compiler feedback:

```
Syntax error on line 2: unpaired '{'.
module main {

```
Reply with your UCLID5 code inside one unique code block.

I can definitely do that! Here is the UCLID5 code:
```
