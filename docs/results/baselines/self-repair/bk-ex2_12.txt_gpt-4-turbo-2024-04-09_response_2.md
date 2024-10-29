```uclid5
module main {
    type location_t = enum { start, select };
    const max : int;

    // Variables
    var nsoda : int;
    var nbeer : int;
    var current_loc : location_t;

    // Initialization
    init {
        nsoda = max;
        nbeer = max;
        current_loc = start;
    }

    // Transition system
    transition
    coin {
        // User inserts a coin
        from start to select
        with true;
    },
    refill {
        // Refill the machine
        from start to start
        with true
        do {
            nsoda := max;
            nbeer := max;
        }
    },
    sget {
        // Get soda
        from select to start
        with nsoda > 0
        do {
            nsoda := nsoda - 1;
        }
    },
    bget {
        // Get beer
        from select to start
        with nbeer > 0
        do {
            nbeer := nbeer - 1;
        }
    },
    ret_coin {
        // Return coin if empty
        from select to start
        with (nsoda = 0 & nbeer = 0);
    };

    // Safety property
    invariant "NonNegativeSoda" : nsoda >= 0;
    invariant "NonNegativeBeer" : nbeer >= 0;
    invariant "LocationCheck" : (current_loc = start) | (current_loc = select);
}

// Instantiate the module
module final_vending_machine = main(max = 100);
```