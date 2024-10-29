(deftype Coin (Finite 10))

(const coin Coin)

(const dispensed_drinks int)

(rule (<= (coin) 10))

(rule (<= (dispensed_drinks) (coin)))

(safety (<= (dispensed_drinks) (coin)))
```