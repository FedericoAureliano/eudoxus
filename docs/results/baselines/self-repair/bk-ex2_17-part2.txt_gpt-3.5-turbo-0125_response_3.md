```uclid
module TrafficLights

const red1 : bool;
const green1 : bool;
const red2 : bool;
const green2 : bool;

const red1_initial = true;
const green1_initial = false;
const red2_initial = true;
const green2_initial = false;

axioms
(init_red1: red1 = red1_initial);
(init_green1: green1 = green1_initial);
(init_red2: red2 = red2_initial);
(init_green2: green2 = green2_initial);

rules
rule turn_red1_to_green1:
  requires red1;
  ensures green1;

rule turn_green1_to_red1:
  requires green1;
  ensures red1;

rule turn_red2_to_green2:
  requires red2;
  ensures green2;

rule turn_green2_to_red2:
  requires green2;
  ensures red2;

end
```