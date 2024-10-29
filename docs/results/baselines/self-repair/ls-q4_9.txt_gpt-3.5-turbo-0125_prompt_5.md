
Fix the following UCLID5 code using the compiler feedback provided below.

```

(define main-light
    (input (mR Bool) (mG Bool) (mY Bool))

(define secondary-light
    (input (sR Bool) (sG Bool) (sY Bool))

(define vehicle-detected
    (input (vehicleDetected Bool))

(define mG Bool)
(define mY Bool)
(define mR Bool)
(define sG Bool)
(define sY Bool)
(define sR Bool)

(define spec
    (when (and (not vehicleDetected) (not mY) (not mR))
        (assert mG)
        (assert sR)
        (assert (not sG))
        (assert (not sY))
        (assert (not mR))
    )
    
    (when (and vehicleDetected (not mY) (not mR))
        (assert mY)
        (assert sR)
        (assert (not sG))
        (assert (not sY))
        (assert (not mR))
    )
    
    (when (and (not vehicleDetected) mY)
        (assert (not mY))
    )
    
    (when (and (not vehicleDetected) mR)
        (assert (not mR))
        (assert mG)
        (assert sY)
        (assert (not sG))
        (assert (not sR))
    )
)

(assert spec)
```

Compiler feedback:

```
Syntax error on tmp.ucl, line 2: end of input expected.
(define main-light

```
Reply with your UCLID5 code inside one unique code block.

I can definitely do that! Here is the UCLID5 code:
```
