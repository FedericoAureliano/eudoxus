lang uclid5

-- Declare philosophers and chopsticks as boolean variables
var phil1 : boolean;
var phil2 : boolean;
var phil3 : boolean;
var phil4 : boolean;
var phil5 : boolean;
var chopstick1 : boolean;
var chopstick2 : boolean;
var chopstick3 : boolean;
var chopstick4 : boolean;
var chopstick5 : boolean;

-- Philosopher 1 can eat if they have both chopsticks
define rule philosopher1_can_eat = (phil1 => chopstick1 /\ chopstick5);

-- Philosopher 2 can eat if they have both chopsticks
define rule philosopher2_can_eat = (phil2 => chopstick1 /\ chopstick2);

-- Philosopher 3 can eat if they have both chopsticks
define rule philosopher3_can_eat = (phil3 => chopstick2 /\ chopstick3);

-- Philosopher 4 can eat if they have both chopsticks
define rule philosopher4_can_eat = (phil4 => chopstick3 /\ chopstick4);

-- Philosopher 5 can eat if they have both chopsticks
define rule philosopher5_can_eat = (phil5 => chopstick4 /\ chopstick5);

-- Add a property to check for deadlock by ensuring at most one philosopher can eat at a time
property deadlock_not_possible = (philosopher1_can_eat + philosopher2_can_eat + philosopher3_can_eat + philosopher4_can_eat + philosopher5_can_eat) <= 1;
```