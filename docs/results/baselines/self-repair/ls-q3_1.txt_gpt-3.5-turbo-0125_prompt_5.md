
Fix the following UCLID5 code using the compiler feedback provided below.

```

-- Define variables
var temp : int;
var count : int;

-- Initial values
temp := 0;
count := 0;

-- Event counter logic
procedure checkTemperature(threshold: int)
begin
    if temp > threshold then
        count := count + 1;
    end
end

-- Main program
begin
    temp := 25;
    checkTemperature(20);
    temp := 22;
    checkTemperature(20);
    temp := 30;
    checkTemperature(20);
    temp := 18;
    checkTemperature(20);
    temp := 25;
    checkTemperature(20);
end;
```

Compiler feedback:

```
Syntax error on tmp.ucl, line 2: end of input expected.
-- Define variables

```
Reply with your UCLID5 code inside one unique code block.

I can definitely do that! Here is the UCLID5 code:
```
