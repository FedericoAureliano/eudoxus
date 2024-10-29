
Fix the following UCLID5 code using the compiler feedback provided below.

```

theory Thermostat_Heater
const X : int = 1
const Y : int = 120

type Temperature = int[X..Y]

var temp : Temperature
var heatOn : bool
var heatOff : bool
var time : int[0..1800]

axioms
  Init:
    time = 0

  TurnOnHeater:
    forall t : Temperature.
      if t <= 20 and time % 30 = 0
      then heatOn = true
  
  TurnOffHeater:
    forall t : Temperature.
      if t > 20 and time % 30 = 0
      then heatOff = true

  StayOnHeat:
    forall t : Temperature.
      if heatOn = true
      then time - time' >= 30

  StayOffHeat:
    forall t : Temperature.
      if heatOff = true
      then time - time' >= 120

  TurnHeatOnAgain:
    forall t : Temperature.
      if heatOff = true and t <= 20 and time % 30 = 0
      then heatOn = true

end
```

Compiler feedback:

```
Syntax error on line 2: cannot find key word module.
theory Thermostat_Heater

```
Reply with your UCLID5 code inside one unique code block.

I can definitely do that! Here is the UCLID5 code:
```
