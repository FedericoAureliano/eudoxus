(set-logic ALL)

(declare-sort TrainState)
(declare-const far TrainState)
(declare-const near TrainState)
(declare-const in TrainState)

(declare-sort GateState)
(declare-const up GateState)
(declare-const down GateState)

(declare-sort ControllerState)
(declare-const state0 ControllerState)
(declare-const state1 ControllerState)
(declare-const state2 ControllerState)
(declare-const state3 ControllerState)

(declare-const train_state TrainState)
(declare-const gate_state GateState)
(declare-const controller_state ControllerState)

(assert (or (= train_state far) (= train_state near) (= train_state in)))
(assert (or (= gate_state up) (= gate_state down)))
(assert (or (= controller_state state0) (= controller_state state1) (= controller_state state2) (= controller_state state3)))

(define-transition train_approaching
  (state0)
  (and (= train_state near) (= controller_state state0))
  ((= controller_state state1))
)

(define-transition gate_lowering
  (state1)
  (and (= gate_state up) (= controller_state state1))
  ((= controller_state state2))
)

(define-transition train_exiting
  (state2)
  (and (= train_state in) (= controller_state state2))
  ((= controller_state state3))
)

(define-transition gate_raising
  (state3)
  (and (= gate_state down) (= controller_state state3))
  ((= controller_state state0))
)

(check-sat)
```