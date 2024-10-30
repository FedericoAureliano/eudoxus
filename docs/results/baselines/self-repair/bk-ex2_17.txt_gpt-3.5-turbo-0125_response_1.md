#lang uclid

var red : boolean;
var green : boolean;

-- initial state
init(red) := true;
init(green) := false;

-- transitions
next(red) :=
  case
    red : green;
    green : red;
  esac;

next(green) :=
  !red;

-- safety property: red and green cannot be true at the same time
system red_exclusive := ! (red && green);