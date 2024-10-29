```uclid
datatype ProcessID = P0 | P1;
datatype State = CRITICAL | NONCRITICAL;

record StateVariables {
    s : int,
    y0 : bool,
    y1 : bool 
}

record ProcessState {
    pid : ProcessID,
    state : State
}

record SystemState {
    p0_state : ProcessState,
    p1_state : ProcessState,
    vars : StateVariables
}

const initial_state : SystemState = {
    p0_state : {pid: P0, state: NONCRITICAL},
    p1_state : {pid: P1, state: NONCRITICAL},
    vars : {s: 1, y0: false, y1: false}
};

// Transition rules
axiom can_enter_critical_section(state: SystemState, pid: ProcessID) {
    (pid = P0) iff (state.vars.y0 = true) && (state.vars.s != 1);
    (pid = P1) iff (state.vars.y1 = true) && (state.vars.s != 0);
}

axiom mutual_exclusion(state: SystemState) {
    state.p0_state.state = CRITICAL implies state.p1_state.state = NONCRITICAL;
    state.p1_state.state = CRITICAL implies state.p0_state.state = NONCRITICAL;
}

axiom starvation_freedom(state: SystemState) {
    always ((state.p0_state.state = NONCRITICAL) => eventually (state.p0_state.state = CRITICAL));
    always ((state.p1_state.state = NONCRITICAL) => eventually (state.p1_state.state = CRITICAL));
}
```