Datatypes
  1: processID
  2: bool

Constants
  P1 : processID
  P2 : processID

Variables
  b1 : bool
  b2 : bool
  x : int

Functions
  wait1() = x := 2;
  wait2() = x := 1;

Transition System
  Process =
    P1
    P2

  Initial_State =
    b1 = false;
    b2 = false;
    x = 1;

  Transitions =
    transition start_wait1:
      if b1 != true then
        b1' = true;
        wait1();
      else
        skip;

    transition start_wait2:
      if b2 != true then
        b2' = true;
        wait2();
      else
        skip;

    transition enter_crit_section_P1:
      if x = 1 then
        x' = 2;
        b1' = false;
      else
        skip;

    transition enter_crit_section_P2:
      if x = 2 then
        x' = 1;
        b2' = false;
      else
        skip;

    transition exit_crit_section_P1:
      skip;

    transition exit_crit_section_P2:
      skip;
```