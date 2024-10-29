```smt2
(set-logic QF_LRA)

(declare-fun temp () Real)
(declare-fun heatOn () Bool)
(declare-fun heatOff () Bool)

(declare-const setpoint Real)
(declare-const upperBound Real)
(declare-const lowerBound Real)

(define-fun setpointValue () Real (20.0))
(define-fun upperBoundValue () Real (22.0))
(define-fun lowerBoundValue () Real (18.0))

(define-fun heating () Bool 
    (and (<= temp upperBound) (<= upperBound setpoint)))

(define-fun cooling () Bool 
    (and (>= temp lowerBound) (>= lowerBound setpoint)))

(declare-fun newHeatingStatus () Bool)

(assert (= newHeatingStatus (not heating)))

(declare-fun newCoolingStatus () Bool)

(assert (= newCoolingStatus (not cooling)))

(assert (or (and heating (not cooling))
            (and cooling (not heating))))

(assert (and (=> heating (not (= temp setpointValue)))
            (=> cooling (not (= temp setpointValue)))))

(assert (=> heating (> temp upperBoundValue)))

(assert (=> cooling (< temp lowerBoundValue)))

(define-fun heatOn () Bool 
    (and heating newCoolingStatus))

(define-fun heatOff () Bool 
    (and cooling newHeatingStatus))

(check-sat)
```