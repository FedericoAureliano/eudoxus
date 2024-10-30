```
(define-variable capacity 5)

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
                   (= (select s i) 0))))

(check-sat)
```