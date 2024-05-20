function power(x :int, pow :int) : int
decreases( pow );
 {
  if pow == 0 then 1 else if pow >= 1 then power(x, pow - 1) * x else 0
}
