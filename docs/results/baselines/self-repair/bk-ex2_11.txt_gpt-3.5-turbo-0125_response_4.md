(define x (input bit))
(define y (output bit))
(define r (register bit))

(init (and (= r #b0) (or (= x #b0) (= x #b1))))

(next (= r (or x r)))

(next (= y (not (xor x r))))

(define-property (always (eventually (= y #b1))))
```