
Fix the following UCLID5 code using the compiler feedback provided below.

```

(define light_on (mk-bool))
(define door_open (mk-bool))
(define time (mk-real))

(declare-const light_on_prev bool)
(declare-const light_on_next bool)
(declare-const time_prev real)
(declare-const time_next real)

(synth-fun dome_light_behavior ((light_on_prev bool) (door_open bool) (time_prev real)) (light_on_next bool time_next)
  ((Start
    (=> (and (not door_open) (= light_on_prev true))
        (and (= light_on_next false) (= time_next 0.0)))
    (Maintain
      (and (<= 0.0 time_prev) (<= time_prev 30.0))
      (=> (and (or door_open (= time_prev 30.0)) (= light_on_prev true))
          (and (= light_on_next false) (= time_next 0.0)))
      (=> (and door_open (< time_prev 30.0) (= light_on_prev true))
          (and (= light_on_next true) (= time_next (+ time_prev 1.0))))
      (=> (and door_open (= time_prev 30.0) (= light_on_prev false))
          (and (= light_on_next false) (= time_next 0.0)))
      (=> (and door_open (< time_prev 30.0) (= light_on_prev false))
          (and (= light_on_next false) (= time_next 0.0)))))))

(assert (forall ((a bool) (b bool) (c real))
          (= (dome_light_behavior a b c) (mk-tuple bool real))))

(check-synth)
```

Compiler feedback:

```
Syntax error on tmp.ucl, line 2: end of input expected.
(define light_on (mk-bool))

```
Reply with your UCLID5 code inside one unique code block.

I can definitely do that! Here is the UCLID5 code:
```
