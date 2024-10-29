
Fix the following UCLID5 code using the compiler feedback provided below.

```

    type Temperature = int;
    type Count = int;

    const threshold : Temperature;

    var temp : Temperature;
    var count : Count;

    init {
        temp = 0;
        count = 0;
    }

    next {
        temp' = choose t : Temperature :: true;
        if (temp > threshold) {
            count' = count + 1;
        } else {
            count' = count;
        }
    }

    // Specification to ensure that the count increments properly above the threshold
    property correct_counting {
        always ((temp > threshold) => (next(count) = count + 1))
    }
}
```

Compiler feedback:

```
Syntax error on tmp.ucl, line 2: end of input expected.
    type Temperature = int;

```
Reply with your UCLID5 code inside one unique code block.

I can definitely do that! Here is the UCLID5 code:
```
