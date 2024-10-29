
Fix the following UCLID5 code using the compiler feedback provided below.

```

-- Declare constants
CONSTANT initial_value : int = 0;

-- Declare inputs
INPUT arrival : bool;
INPUT departure : bool;

-- Declare outputs
OUTPUT display : int;

-- Declare state variable
STATE counter : int = initial_value;

-- Model the system
WHEN arrival THEN
    counter := counter + 1;
    display := counter;
END;

WHEN departure THEN
    counter := counter - 1;
    display := counter;
END;
```

Compiler feedback:

```
Syntax error on tmp.ucl, line 2: end of input expected.
-- Declare constants

```
Reply with your UCLID5 code inside one unique code block.

I can definitely do that! Here is the UCLID5 code:
```
