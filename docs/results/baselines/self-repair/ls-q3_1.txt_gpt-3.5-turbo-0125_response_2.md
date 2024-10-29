-- Define variables
var temp : int
var count : int

-- Initial values
temp := 0
count := 0

-- Event counter logic
procedure checkTemperature(threshold: int)
begin
    if temp > threshold then
        count := count + 1
    end
end

-- Main program
begin
    temp := 25
    checkTemperature(20)
    temp := 22
    checkTemperature(20)
    temp := 30
    checkTemperature(20)
    temp := 18
    checkTemperature(20)
    temp := 25
    checkTemperature(20)
end
```