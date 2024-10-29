```uclid
module main {
  type location_t = enum { OUT, WAIT, CRIT };
  var b1, b2 : boolean;
  var x : [1..2];
  var loc1, loc2 : location_t;

  init {
    loc1 = OUT;
    loc2 = OUT;
    b1 = false;
    b2 = false;
    x = 1;
  }

  next(loc1) {
    case
      loc1 == OUT : {WAIT} if !b1;
      loc1 == WAIT : {CRIT} if x == 1 || !b2;
      loc1 == CRIT : {OUT};
      true : loc1;
    esac
  }

  next(b1) {
    case
      loc1 == OUT && loc1' == WAIT : true;
      loc1 == CRIT && loc1' == OUT : false;
      true : b1;
    esac
  }

  next(loc2) {
    case
      loc2 == OUT : {WAIT} if !b2;
      loc2 == WAIT : {CRIT} if x == 2 || !b1;
      loc2 == CRIT : {OUT};
      true : loc2;
    esac
  }

  next(b2) {
    case
      loc2 == OUT && loc2' == WAIT : true;
      loc2 == CRIT && loc2' == OUT : false;
      true : b2;
    esac
  }

  next(x) {
    case
      loc1 == OUT && loc1' == WAIT : 2;
      loc2 == OUT && loc2' == WAIT : 1;
      true : x;
    esac
  }

  invariant "mutual_exclusion" {
    !(loc1 == CRIT && loc2 == CRIT);
  }
}
```

This code defines a UCLID5 module named `main`, which models the behavior of processes P1 and P2 as described.

- We use an enum type `location_t` for maintaining states of each process: `OUT`, `WAIT`, and `CRIT`.
- The boolean variables `b1` and `b2` represent whether each process is either waiting or in its critical section.
- The variable `x` represents which process's turn it is currently.

For each variable, a `next` function is defined:

- `loc1` and `loc2` transition between the OUT, WAIT, and CRIT states based on the described conditions.
- `b1` and `b2` are set or reset during transitions.
- `x` changes values when one process transitions into the waiting state, granting the turn to the other process.

The invariant `mutual_exclusion` ensures no two processes are in their critical sections at the same time, reflecting a basic property of mutual exclusion.