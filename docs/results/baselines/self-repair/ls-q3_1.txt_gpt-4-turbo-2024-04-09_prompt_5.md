
Fix the following UCLID5 code using the compiler feedback provided below.

```

module main {
    type Temperature = int;
    type Count = int;

    const threshold : Temperature;

    var temp : Temperature;
    var count : Count;

    init {
        temp := 0;
        count := 0;
    }

    next {
        temp' = choose t : Temperature :: true;
        if (temp > threshold) {
            count' = count + 1;
        } else {
            count' = count;
        }
    }

    property correct_counting {
        always ((temp > threshold) => (next(count) = count + 1))
    }
}
```

Compiler feedback:

```
Syntax error on line 12: Syntax Error in Expression.
        temp := 0;

```
Reply with your UCLID5 code inside one unique code block.

I can definitely do that! Here is the UCLID5 code:
```
