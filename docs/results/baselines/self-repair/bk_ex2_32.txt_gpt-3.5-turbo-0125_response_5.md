module c_d_channel {
    input c: bool;
    output d: bool;
}

module sender {
    const TIMEOUT_LIMIT: int;

    input S: bool;
    input m: int;
    input b: bool;
    output c: bool;

    var timeout_counter: int;

    assume TIMEOUT_LIMIT > 0;

    init {
        assert timeout_counter < TIMEOUT_LIMIT;
        timeout_counter := 0;
    }

    transition {
        if S == true && c == false {
            c' = true;
        } else {
            c' = c;
        }
    }

    transition {
        if c == true && d == true && b == true {
            timeout_counter' = 0;
        } else {
            timeout_counter' = timeout_counter + 1;
        }
    }
}

module receiver {
    input c: bool;
    input d: bool;
    input b: bool;
    output R: bool;

    init {
        R := false;
    }

    transition {
        if c == true && d == true {
            R := not(b);
        }
    }
}
```