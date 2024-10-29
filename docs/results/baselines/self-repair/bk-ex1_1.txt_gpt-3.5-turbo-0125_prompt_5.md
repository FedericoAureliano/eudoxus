
Fix the following UCLID5 code using the compiler feedback provided below.

```

(const
  x: int;

(inv
  (and 
    (<= x 200)
    (>= x 0)
  )
)

(inc
  (while true do
    (if (< x 200) 
      (update x (+ x 1))
    fi
    )
  )
)

(dec
  (while true do
    (if (> x 0) 
      (update x (- x 1))
    fi
    )
  )
)

(reset
  (while true do
    (if (= x 200)
      (update x 0)
    fi
    )
  )
)
```

Compiler feedback:

```
Syntax error on tmp.ucl, line 2: end of input expected.
(const

```
Reply with your UCLID5 code inside one unique code block.

I can definitely do that! Here is the UCLID5 code:
```
