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

This code models a thermostat controlling a heater system with the specified behavior. If you need any adjustments or further details, please let me know!