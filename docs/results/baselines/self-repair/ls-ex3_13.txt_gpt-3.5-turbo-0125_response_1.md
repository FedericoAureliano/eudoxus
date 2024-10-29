(machine 
  (state red
    (transition (after 60 (set green)))
  )
  (state green
    (transition 
      (when pedestrian (set yellow))
      (after 60 (set pending))
    )
  )
  (state yellow
    (transition (after 5 (set red)))
  )
  (state pending
    (transition (after (- 60 count) (set yellow)))
  )
  (variable count 0)
  (variable pedestrian false)
  (variable sigG false)
  (variable sigY false)
  (variable sigR false)
)
```