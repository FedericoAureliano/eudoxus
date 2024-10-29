```
module main {
  type location_t = enum { OUT, WAIT, CRIT };
  var b1, b2 : boolean;
  var x : int;
  var loc1, loc2 : location_t;

  init {
    loc1 = OUT;
    loc2 = OUT;
    b1 = false;
    b2 = false;
    x = 1;
  }

  next(loc1) =
    case
      loc1 == OUT : {WAIT} if !b1;
      loc1 == WAIT : {CRIT} if x == 1 || !b2;
      loc1 == CRIT : {OUT};
      true : loc1;
    esac;

  next(b1) =
    case
      loc1 == OUT && loc1' == WAIT : true;
      loc1 == CRIT && loc1' == OUT : false;
      true : b1;
    esac;

  next(loc2) =
    case
      loc2 == OUT : {WAIT} if !b2;
      loc2 == WAIT : {CRIT} if x == 2 || !b1;
      loc2 == CRIT : {OUT};
      true : loc2;
    esac;

  next(b2) =
    case
      loc2 == OUT && loc2' == WAIT : true;
      loc2 == CRIT && loc2' == OUT : false;
      true : b2;
    esac;

  next(x) =
    case
      loc1 == OUT && loc1' == WAIT : 2;
      loc2 == OUT && loc2' == WAIT : 1;
      true : x;
    esac;

  invariant "mutual_exclusion" {
    !(loc1 == CRIT && loc2 == CRIT);
  }
}
```