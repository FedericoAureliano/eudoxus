
Fix the following UCLID5 code using the compiler feedback provided below.

```

(define capacity 5)

(define-variable s (Array Int capacity))

(define-transition top
  (=> (< 0 (select s 0))
      (array-equals s s)))

(define-transition pop
  (=> (< 0 (select s 0))
      (forall ((i Int))
              (=> (< i (- capacity 1))
                  (let ((temp (select s (+ i 1))))
                    (array-equals s (store s i temp))))))

(define-transition push
  (=> (< 0 (select s (- capacity 1)))
      (forall ((i Int))
              (=> (< i (- capacity 1))
                  (let ((temp (select s i)))
                    (array-equals s (store s (+ i 1) temp))))))

(define-init
  (and (forall ((i Int))
               (=> (< i capacity)
                   (= (select s i) 0)))))

(check-sat)
```

Compiler feedback:

```
Syntax error on tmp.ucl, line 2: end of input expected.
(define capacity 5)

```
Reply with your UCLID5 code inside one unique code block.

I can definitely do that! Here is the UCLID5 code:
```
