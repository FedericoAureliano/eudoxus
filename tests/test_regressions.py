import ast

from uclid_lm_ir.printer import print_uclid5
from uclid_lm_ir.utils import assert_equal


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
    output = print_uclid5(python)
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
    output = print_uclid5(python)
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
    output = print_uclid5(python)
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
    output = print_uclid5(python)
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
    instance m1 : StateMachineA(data : (data), inc : (inc));
    // Instance argument must be a local variable name, not an expression.
    instance m2 : StateMachineB(data : (data), inc : (??));

    init {
        inc = false;
    }

    next {
        inc' = !inc;
    }
}
"""
    python = ast.parse(code)
    output = print_uclid5(python)
    assert_equal(output, expected)
