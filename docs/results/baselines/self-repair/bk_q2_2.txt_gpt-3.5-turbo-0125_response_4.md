```

const N : int = 0;

type processType = { P1, P2, P3 };

var x : int;

procedure main()
  x := 0;
  call P1 || P2 || P3;
end

procedure P1()
  for i : 1..N {
    call LOAD(x);
    call INC(x);
    call STORE(x);
  }
end

procedure P2()
  for i : 1..N {
    call LOAD(x);
    call INC(x);
    call STORE(x);
  }
end

procedure P3()
  for i : 1..N {
    call LOAD(x);
    call INC(x);
    call STORE(x);
  }
end

property eventuallyHaltWithX2()
  x = 2
end
```