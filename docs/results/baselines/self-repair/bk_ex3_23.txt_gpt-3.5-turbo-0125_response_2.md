```uclid
module traffic_light_system

BV: red yellow green;
VAR prev_phase: BV;

INIT:
  red = 0;
  yellow = 0;
  green = 0;
  prev_phase = 0;

TRANS:
  OR(red = prev_phase & yellow = 1, yellow = prev_phase & green = 1);

NEXT:
  red' = OR(prev_phase = yellow, prev_phase = red & yellow = 1);
  yellow' = OR(prev_phase = green, prev_phase = yellow & red = 1);
  green' = OR(prev_phase = red, prev_phase = green & yellow = 1);
  prev_phase' = prev_phase;

SPEC:
  G(red -> X(yellow));

endmodule;
```