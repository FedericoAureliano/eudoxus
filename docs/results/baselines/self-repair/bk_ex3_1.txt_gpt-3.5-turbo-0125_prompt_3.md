
Fix the following UCLID5 code using the compiler feedback provided below.

```

(define-type Light
  (Enum green1 red1 green2 red2))

(define-type Action
  (Enum A B))

(define-type Transition
  (Tuple Light 
         Action 
         Light))

(declare-const traffic_light1 Light)
(declare-const traffic_light2 Light)

(define transition1
  (let ((prev-state traffic_light1)
        (next-state (mux (= traffic_light1 green1) red1 green1)))
    (assert (= next-state traffic_light1))
    (assert (or (and (= prev-state green1) (= next-state red1))
                (and (= prev-state red1) (= next-state green1)))
    prev-state))

(define transition2
  (let ((prev-state traffic_light2)
        (next-state (mux (= traffic_light2 green2) red2 green2)))
    (assert (= next-state traffic_light2))
    (assert (or (and (= prev-state green2) (= next-state red2))
                (and (= prev-state red2) (= next-state green2)))
    prev-state))

(assert (not (and (= traffic_light1 green1) (= traffic_light2 green2))))

(check-sat)
```

Compiler feedback:

```
Syntax error on tmp.ucl, line 2: end of input expected.
(define-type Light

```
Reply with your UCLID5 code inside one unique code block.

I can definitely do that! Here is the UCLID5 code:
```
