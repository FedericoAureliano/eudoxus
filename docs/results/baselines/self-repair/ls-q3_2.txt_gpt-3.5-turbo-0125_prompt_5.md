
Fix the following UCLID5 code using the compiler feedback provided below.

```

module Thermostat_Heater

const X : int = 1;
const Y : int = 120;

type Temperature = array[X..Y] of int;

var temp : Temperature;
var heatOn : bool;
var heatOff : bool;
var time : int[X..1800];

axioms
  Init:
    time = 0;

  TurnOnHeater:
    forall t : Temperature
    if t <= 20 && time % 30 = 0
    then heatOn = true;
  
  TurnOffHeater:
    forall t : Temperature
    if t > 20 && time % 30 = 0
    then heatOff = true;

  StayOnHeat:
    forall t : Temperature
    if heatOn
    then time - time' >= 30;

  StayOffHeat:
    forall t : Temperature
    if heatOff
    then time - time' >= 120;

  TurnHeatOnAgain:
    forall t : Temperature
    if heatOff && t <= 20 && time % 30 = 0
    then heatOn = true;

end
```

Compiler feedback:

```
Syntax error on line 2: loss of '{'.
module Thermostat_Heater

```
Reply with your UCLID5 code inside one unique code block.

I can definitely do that! Here is the UCLID5 code:
```
