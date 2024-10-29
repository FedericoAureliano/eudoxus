
Fix the following UCLID5 code using the compiler feedback provided below.

```

module main {
  type mem_val_t = integer;
  var x : mem_val_t;
  
  init {
    x = 0;
  }

  function LoadX(): mem_val_t {
    return x;
  }

  function IncX(y: mem_val_t): mem_val_t {
    return y + 1;
  }

  procedure StoreX(y: mem_val_t) {
    x = y;
  }

  procedure OneRound() {
    var y : mem_val_t;
    var z : mem_val_t;
    y = LoadX();
    z = IncX(y);
    call StoreX(z);
  }

  procedure P1() {
    var i : integer;
    for (i := 1; i <= 10; i := i + 1) {
      call OneRound();
    }
  }

  procedure P2() {
    var i : integer;
    for (i := 1; i <= 10; i := i + 1) {
      call OneRound();
    }
  }
  
  procedure P3() {
    var i : integer;
    for (i := 1; i <= 10; i := i + 1) {
      call OneRound();
    }
  }

  control {
    parallel {
      call P1();
      call P2();
      call P3();
    }
  }

  safety property x_equals_2 {
    x == 2
  }
}
```

Compiler feedback:

```
Syntax error on line 10: .
  function LoadX(): mem_val_t {

```
Reply with your UCLID5 code inside one unique code block.

I can definitely do that! Here is the UCLID5 code:
```
