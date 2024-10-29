```

(const
  x: int;
)

(inv
  (and 
    (<= x 200)
    (>= x 0)
  )
)

(inc
  (while true do
    (if (< x 200) 
      (update x (+ x 1))
    fi
    )
  )
)

(dec
  (while true do
    (if (> x 0) 
      (update x (- x 1))
    fi
    )
  )
)

(reset
  (while true do
    (if (= x 200)
      (update x 0)
    fi
    )
  )
)
```