import ast

from eudoxus.compiler import compile_to_uclid5
from eudoxus.utils import assert_equal


def test_intersection():
    code = """
class IntersectionModule(Module):
    def types(self):
        self.CarState = Enum('CarState', 'moving stopped')
        self.LightState = Enum('LightState', 'red green')

    def locals(self):
        self.car1 = self.CarState
        self.car2 = self.CarState
        self.light1 = self.LightState
        self.light2 = self.LightState

    def init(self):
        self.car1 = stopped
        self.car2 = stopped
        self.light1 = red
        self.light2 = red

    def next(self):
        if self.light1 == green:
            self.car1 = moving
        else:
            self.car1 = stopped
"""

    expected = """
module IntersectionModule {
    type CarState = enum { moving, stopped };
    type LightState = enum { red, green };
    var car1 : CarState;
    var car2 : CarState;
    var light1 : LightState;
    var light2 : LightState;

    init {
        car1 = stopped;
        car2 = stopped;
        light1 = red;
        light2 = red;
    }

    next {
        if (light1 == green) {
            car1' = moving;
        } else {
            car1' = stopped;
        }
    }
}
"""
    python = ast.parse(code)
    output = compile_to_uclid5(python)
    assert_equal(output, expected)


def test_array_and_synonym():
    code = """
class Module:
    def types(self):
        self.T = BitVector(8)

    def locals(self):
        self.x = Array(index=BitVector(8), value=self.T)
"""

    expected = """
module Module {
    type T = bv8;
    var x : [bv8]T;
}
"""
    python = ast.parse(code)
    output = compile_to_uclid5(python)
    assert_equal(output, expected)


def test_clock():
    code = """
class Clock(Module):
    def outputs(self):
        self.tick = Bool()

    def next(self):
        self.tick = Not(self.tick)

class TickCounter(Module):
    def locals(self):
        self.count = BitVector(3)

    def inputs(self):
        self.clock_tick = Bool()

    def init(self):
        self.count = 0

    def next(self):
        if And(self.clock_tick, self.count < 7):
            self.count = self.count + 1
        else:
            self.count = 0

    def instances(self):
        self.clock = Clock(tick=self.clock_tick)

    def specification(self):
        return And(self.count >= 0, self.count <= 7)

class System(Module):
    def instances(self):
        self.tick_counter = TickCounter()

    def specification(self):
        return self.tick_counter.specification()

    def proof(self):
        induction(1)
"""

    expected = """
module Clock {
    output tick : boolean;

    next {
        tick' = !tick;
    }
}

module TickCounter {
    var count : bv3;
    input clock_tick : boolean;

    init {
        count = 0;
    }

    next {
        if (clock_tick && count < 7) {
            count' = count + 1;
        } else {
            count' = 0;
        }
    }

    instance clock : Clock(tick : (clock_tick));

    invariant spec: count >= 0 && count <= 7;
}

module System {
    instance tick_counter : TickCounter();

    invariant spec: ??;

    control {
        induction(1);
        check;
        print_results();
    }
}
"""
    python = ast.parse(code)
    output = compile_to_uclid5(python)
    assert_equal(output, expected)


def test_clock_2():
    code = """
class Clock(Module):
    def outputs(self):
        self.tick = Boolean()

    def init(self):
        self.tick = False

    def next(self):
        self.tick = Not(self.tick)

class TickCounter(Module):
    def types(self):
        self.T = BitVector(3)

    def locals(self):
        self.count = self.T

    def inputs(self):
        self.tick = Boolean()

    def init(self):
        self.count = 0

    def specification(self):
        return self.count <= 7


# Connecting the modules

class Main(Module):
    def instances(self):
        self.clock = Clock()
        self.counter = TickCounter(tick=self.clock.tick)

    def proof(self):
        induction(1)

    def init(self):
        self.clock.init()
        self.counter.init()

    def next(self):
        self.clock.next()
        self.counter.next()
"""

    expected = """
module Clock {
    output tick : boolean;

    init {
        tick = false;
    }

    next {
        tick' = !tick;
    }
}

module TickCounter {
    type T = bv3;
    var count : T;
    input tick : boolean;

    init {
        count = 0;
    }

    invariant spec: count <= 7;
}

module Main {
    instance clock : Clock();
    // Instance argument must be a local variable name, not an expression.
    instance counter : TickCounter(tick : (??));

    control {
        induction(1);
        check;
        print_results();
    }

    init {
        ??;
        ??;
    }

    next {
        next(clock);
        next(counter);
    }
}
"""
    python = ast.parse(code)
    output = compile_to_uclid5(python)
    assert_equal(output, expected)


def test_two_state_machines():
    code = """
class StateMachineA(Module):
    def types(self):
        self.State = Enum('idle', 'send', 'wait')

    def locals(self):
        self.state = self.State

    def shared_vars(self):
        self.data = BitVector(8)

    def inputs(self):
        self.inc = Boolean()

    def init(self):
        self.state = 'idle'
        self.data = BitVector(8)(0)

    def next(self):
        with case('idle'):
            self.data = self.data + 1 if self.inc else self.data
            self.state = 'send' if self.inc else 'idle'
        with case('send'):
            self.state = 'wait'
        with case('wait'):
            self.state = 'idle' if not self.inc else 'wait'
        default(None)

class StateMachineB(Module):
    def types(self):
        self.State = Enum('idle', 'receive', 'wait')

    def locals(self):
        self.state = self.State

    def shared_vars(self):
        self.data = BitVector(8)

    def inputs(self):
        self.inc = Boolean()

    def init(self):
        self.state = 'idle'
        self.data = BitVector(8)(0)

    def next(self):
        with case('idle'):
            self.state = 'receive' if self.inc else 'idle'
        with case('receive'):
            self.data = self.data + 1
            self.state = 'wait'
        with case('wait'):
            self.state = 'idle' if not self.inc else 'wait'
        default(None)

class CommunicatingStateMachines(Module):
    def instances(self):
        self.m1 = StateMachineA(data=self.data, inc=self.inc)
        self.m2 = StateMachineB(data=self.data, inc=~self.inc)

    def init(self):
        self.inc = False

    def next(self):
        self.inc = ~self.inc"""
    expected = """
module StateMachineA {
    type State = enum { idle, send, wait };
    var state : State;
    sharedvar data : bv8;
    input inc : boolean;

    init {
        state = idle;
        data = 0bv8;
    }

    next {
        if (??) {
            data' = if inc then data + 1 else data;
            state' = if inc then send else idle;
        }
        if (??) {
            state' = wait;
        }
        if (??) {
            state' = if !inc then idle else wait;
        }
        ??;
    }
}

module StateMachineB {
    type State = enum { idle, receive, wait };
    var state : State;
    sharedvar data : bv8;
    input inc : boolean;

    init {
        state = idle;
        data = 0bv8;
    }

    next {
        if (??) {
            state' = if inc then receive else idle;
        }
        if (??) {
            data' = data + 1;
            state' = wait;
        }
        if (??) {
            state' = if !inc then idle else wait;
        }
        ??;
    }
}

module CommunicatingStateMachines {
    instance m1 : StateMachineA(data : (??), inc : (??));
    // Instance argument must be a local variable name, not an expression.
    instance m2 : StateMachineB(data : (??), inc : (??));

    init {
        ?? = false;
    }

    next {
        ?? = !??;
    }
}
"""
    python = ast.parse(code)
    output = compile_to_uclid5(python)
    assert_equal(output, expected)


def test_ep0():
    code = """
class MyModule(Module):
    '''A class to represent a UCLID5 module.'''

    def types(self):
        '''Defines a 128-bit type called T.'''
        self.T = BitVector(128)

    def locals(self):
        '''Defines local variables.'''
        # integer variables
        self.a = Integer()
        self.b = Integer()

        # bitvector variables
        self.x = self.T
        self.y = self.T

    def init(self):
        '''Initializes variables.'''
        self.a = 6
        self.b = 2

        self.x = 1 << 127 # 2^127
        self.y = 2

        assert self.a / self.b == 3 # check integer division
        assert self.x / self.y == 1 << 126 # check bitvector division
        # check signed & unsigned division are different
        assert self.x.sdiv(self.y) != self.x.udiv(self.y)

    def next(self):
        '''Defines the transition relation.'''
        next_values = [2, 3, 10, 100, 1 << 63, 1 << 127]
        for value in next_values:
            self.a = self.a * value
            self.b = self.b * value
            # Check that we can correctly divide two integers
            assert self.a / self.b == (self.a // self.b)

            self.x = self.x * value
            self.y = self.y * value
            # Check that we can correctly divide two bitvectors
            assert self.x / self.y == (self.x // self.y)
            # Check that signed and unsigned division are different
            assert self.x.sdiv(self.y) != self.x.udiv(self.y)

    def specification(self):
        '''Defines the invariant properties.'''
        # Check that we can correctly divide two integers
        assert self.a / self.b == (self.a // self.b)

        # Check that we can correctly divide two bitvectors
        assert self.x / self.y == (self.x // self.y)

        # Check that signed and unsigned division report different results for
        # very big bitvectors
        assert self.x.sdiv(self.y) != self.x.udiv(self.y)

        return True

    def proof(self):
        '''Defines the control block.'''
        # Proof by induction
        self.init()
        self.next()
        return self.specification()"""
    expected = """
module MyModule {
  // A class to represent a UCLID5 module.
  // Defines a 128-bit type called T.
  type T = bv128;
  // Defines local variables.
  var a : integer;
  var b : integer;
  var x : T;
  var y : T;
  init {
    // Initializes variables.
    a = 6;
    b = 2;
    x = 1 << 127;
    y = 2;
    assert(a / b == 3);
    assert(x / y == 1 << 126);
    assert(?? != ??);
  }
  next {
    // Defines the transition relation.
    ?? = ??;
    for value in ?? {
        a' = a * value;
        b' = b * value;
        assert(a / b == a // b);
        x' = x * value;
        y' = y * value;
        assert(x / y == x // y);
        assert(?? != ??);
    }
  }
  // Defines the invariant properties.
  invariant spec: a / b == a // b;
  invariant spec_2: x / y == x // y;
  invariant spec_3: ?? != ??;
  invariant spec_4: true;
  control {
    // Defines the control block.
  }
}"""
    python = ast.parse(code)
    output = compile_to_uclid5(python)
    assert_equal(output, expected)


def test_havoc():
    code = """from random import randint

class SimpleModule(Module):
    def types(self):
        pass

    def locals(self):
        self.v = Integer()

    def inputs(self):
        pass

    def outputs(self):
        pass

    def shared_vars(self):
        pass

    def instances(self):
        pass

    def init(self):
        self.v = 0

    def next(self):
        self.v = randint(-100, 100)
        assert self.v == 0

    def specification(self):
        return self.v == 0

    def proof(self):
        unroll(1)"""
    expected = """module SimpleModule {
  var v : integer;
  init {
    v = 0;
  }
  next {
    havoc(v);
    assert(v == 0);
  }
  invariant spec: v == 0;
  control {
    bmc(1);
    check;
    print_results();
  }
}"""
    python = ast.parse(code)
    output = compile_to_uclid5(python)
    assert_equal(output, expected)


def test_nonstandard_bitvecs_and_havoc():
    code = """
from z3 import *

class SimpleModule(Module):
    '''A simple UCLID5 module.'''

    def locals(self):
        '''Define the local variable.'''
        self.x = BitVector('x', 32)

    def init(self):
        '''Initialise the variable to 0.'''
        self.x = BitVecVal(0, 32)

    def next(self):
        '''Havoc the variable and assert that it remains equal to 0.'''
        self.x = BitVec('x', 32) # HaVoc
        assert(self.x == 0)

    def proof(self):
        '''Use bounded model checking with an unrolling of 1.'''
        s = Solver()
        s.add(self.x == 0) # initial state
        s.add(self.x != 0) # after first unrolling
        result = s.check()
        assert(result == unsat)

# Instantiate and check the module
m = SimpleModule()
m.proof()"""
    expected = """module SimpleModule {
  // A simple UCLID5 module.
  // Define the local variable.
  var x : bv32;
  init {
    // Initialise the variable to 0.
    x = 0bv32;
  }
  next {
    // Havoc the variable and assert that it remains equal to 0.
    havoc(x);
    assert(x == 0);
  }
  control {
    // Use bounded model checking with an unrolling of 1.
  }
}"""
    python = ast.parse(code)
    output = compile_to_uclid5(python)
    assert_equal(output, expected)
