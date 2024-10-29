```uclid
type Loc = 0 | 1;

const initialLoc: Loc = 0;

type Action = {x: int | true};

function step(a: Action, l: Loc): Loc {
  if l = 0 then
    if a.x = 2*x then 1 else 0
  else
    if a.x = x+1 then 0 else 1
  end
}

var x: int = 3;

procedure A() {
  x := 2 * x;
}

procedure B() {
  x := x + 1;
}

procedure Main() {
  var a: Action;
  var l: Loc = initialLoc;
  
  while true {
    if l = 0 then {
      a := {x: 2*x};
      A();
    } else {
      a := {x: x+1};
      B();
    }
    
    l := step(a, l);
  }
}
```