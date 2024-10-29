const N : int;

type processType = { P1, P2, P3 };

var x : int;

procedure main()
  x := 0;
  call P1 || P2 || P3;
end

procedure P1()
  for i : 1..N
    call LOAD(x);
    call INC(x);
    call STORE(x);
  end
end

procedure P2()
  for i : 1..N
    call LOAD(x);
    call INC(x);
    call STORE(x);
  end
end

procedure P3()
  for i : 1..N
    call LOAD(x);
    call INC(x);
    call STORE(x);
  end
end

property eventuallyHaltWithX2()
  x = 2
end

```
This UCLID5 code defines the processes P1, P2, and P3 as described in the task, and specifies the main process that initializes x to 0 and runs the parallel program. The property eventuallyHaltWithX2 checks if there exists an execution where x halts with the value 2.