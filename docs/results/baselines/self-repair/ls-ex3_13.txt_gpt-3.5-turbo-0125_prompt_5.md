
Fix the following UCLID5 code using the compiler feedback provided below.

```


(machine
  (state red
    (transition (after 60 (set green)))
  )
  (state green
    (transition 
      (when pedestrian (set yellow))
      (after 60 (set pending))
    )
  )
  (state yellow
    (transition (after 5 (set red)))
  )
  (state pending
    (transition (after (- 60 count) (set yellow)))
  )
  (variable count 0)
  (variable pedestrian false)
  (variable sigG false)
  (variable sigY false)
  (variable sigR false)
)
```

Compiler feedback:

```
Syntax error on tmp.ucl, line 3: end of input expected.
(machine

```
Reply with your UCLID5 code inside one unique code block.

I can definitely do that! Here is the UCLID5 code:
```
