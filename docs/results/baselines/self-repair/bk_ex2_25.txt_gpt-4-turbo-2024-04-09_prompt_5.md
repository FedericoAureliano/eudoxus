
Fix the following UCLID5 code using the compiler feedback provided below.

```

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

  next(loc1) :=
    case
      loc1 == OUT : WAIT if !b1;
      loc1 == WAIT : CRIT if x == 1 || !b2;
      loc1 == CRIT : OUT;
      default : loc1;
    esac;

  next(b1) :=
    case
      loc1 == OUT && loc1' == WAIT : true;
      loc1 == CRIT && loc1' == OUT : false;
      default : b1;
    esac;

  next(loc2) :=
    case
      loc2 == OUT : WAIT if !b2;
      loc2 == WAIT : CRIT if x == 2 || !b1;
      loc2 == CRIT : OUT;
      default : loc2;
    esac;

  next(b2) :=
    case
      loc2 == OUT && loc2' == WAIT : true;
      loc2 == CRIT && loc2' == OUT : false;
      default : b2;
    esac;

  next(x) :=
    case
      loc1 == OUT && loc1' == WAIT : 2;
      loc2 == OUT && loc2' == WAIT : 1;
      default : x;
    esac;

  invariant "Mutual Exclusion" {
    !(loc1 == CRIT && loc2 == CRIT);
  }
}
```

Compiler feedback:

```
Syntax error on tmp.ucl, line 2: end of input expected.
  type location_t = enum { OUT, WAIT, CRIT };

```
Reply with your UCLID5 code inside one unique code block.

I can definitely do that! Here is the UCLID5 code:
```
