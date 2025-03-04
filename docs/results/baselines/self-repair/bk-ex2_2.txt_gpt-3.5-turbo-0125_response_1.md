; Define the state space
(declare-datatypes () ((State pay select soda beer)))

; Define the initial state
(declare-const I State)
(assert (= I pay))

; Define the actions
(declare-const insert_coin Bool)
(declare-const get_soda Bool)
(declare-const get_beer Bool)

; Define the transition system
(define-transition-system TS
  (states (state pay select soda beer))
  (init pay)
  (transitions
    (transition 
      pay 
      (and insert_coin (not get_soda) (not get_beer)) 
      select)
    (transition 
      select 
      get_soda 
      soda)
    (transition 
      select 
      get_beer 
      beer)))

; Define LTL property
(define-property Only_Deliver_After_Payment
  (G (=> (and (state TS soda) (not (state TS pay)))
         (state TS pay))))

; Check the property
(check-synth Only_Deliver_After_Payment)
```