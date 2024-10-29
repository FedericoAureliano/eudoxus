L1 : enum {green, yellow, red, amber};
L2 : enum {green, yellow, red, amber};
L3 : enum {green, yellow, red, amber};
L4 : enum {green, yellow, red, amber};

C : contr[
  step1 : (L1 = green) & (L3 = green) & (L2 = green) & (L4 = green) -> (L1 = yellow) & (L3 = yellow);
  step2 : (L1 = yellow) & (L3 = yellow) -> (L1 = red) & (L3 = red) & (L2 = green);
  step3 : (L2 = green) -> (L2 = yellow);
  step4 : (L2 = yellow) -> (L2 = red) & (L4 = green);
  step5 : (L4 = green) -> (L4 = yellow);
  step6 : (L4 = yellow) -> (L4 = red) & (L1 = green) & (L3 = green);
];
``` 

This code creates the model of the street junction with 4 traffic lights and a controller that switches the green lights in the specified order.