
Fix the following UCLID5 code using the compiler feedback provided below.

```

module main {
    type Temperature;
    type Count;

    const threshold : Temperature;

    var temp : Temperature;
    var count : Count;

    init {
        temp = 0;
        count = 0;
    }

    next(temp) {
        temp' = choose t : Temperature :: t;
    }

    next(count) {
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
Syntax error on line 16: Syntax Error after keyword next.
    next(temp) {

```
Reply with your UCLID5 code inside one unique code block.

I can definitely do that! Here is the UCLID5 code:
```
