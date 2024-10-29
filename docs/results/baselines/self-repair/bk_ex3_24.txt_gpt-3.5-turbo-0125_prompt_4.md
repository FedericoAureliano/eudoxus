
Fix the following UCLID5 code using the compiler feedback provided below.

```

(deftype Coin (Finite (Range 0 10)))

(const coin Coin)

(const dispensed_drinks int)

(rule (<= (coin) 10))

(rule (<= (dispensed_drinks) (coin)))

(safety (<= (dispensed_drinks) (coin)))
```

Compiler feedback:

```
Syntax error on tmp.ucl, line 2: end of input expected.
(deftype Coin (Finite (Range 0 10)))

```
Reply with your UCLID5 code inside one unique code block.

I can definitely do that! Here is the UCLID5 code:
```
