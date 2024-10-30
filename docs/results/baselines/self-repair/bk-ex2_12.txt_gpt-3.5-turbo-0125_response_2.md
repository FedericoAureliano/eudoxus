```uclid
(set-logic QF_UFLIA)

(declare-fun nsoda () Int)
(declare-fun nbeer () Int)

(declare-const max Int)

(declare-const sget Bool)
(declare-const bget Bool)
(declare-const refill Bool)
(declare-const coin Bool)
(declare-const ret_coin Bool)

(assert (=> coin (= nsoda nsoda)))
(assert (=> coin (= nbeer nbeer)))

(assert (=> refill (and (= nsoda max) (= nbeer max))))

(assert (=> sget (>= nsoda 1)))
(assert (=> bget (>= nbeer 1)))

(assert (=> ret_coin (and (= nsoda 0) (= nbeer 0)))

(assert (forall ((x Int)) (=> (and (= x nsoda) coin) (= x nsoda)))
(assert (forall ((x Int)) (=> (and (= x nbeer) coin) (= x nbeer)))

(assert (forall ((x Int)) (=> (and (= x nsoda) ret_coin) (= x nsoda)))
(assert (forall ((x Int)) (=> (and (= x nbeer) ret_coin) (= x nbeer)))

(assert (forall ((x Int)) (=> (and (= x nsoda) refill) (= x max)))
(assert (forall ((x Int)) (=> (and (= x nbeer) refill) (= x max)))

(assert (forall ((x Int)) (=> (and (= x nsoda) sget) (= (- x 1) nsoda)))
(assert (forall ((x Int)) (=> (and (= x nbeer) bget) (= (- x 1) nbeer)))

(check-sat)
```