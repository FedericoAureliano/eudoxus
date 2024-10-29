```module main {
    type MessageType;
    var S: Sender;
    var R: Receiver;

    // Channel c for sender to receiver with potential loss of data
    // Channel d is perfect
    var c: [MessageType] boolean;
    var d: boolean;

    init {
        d := false;
        forall (m: MessageType) :: c[m] := false;
    }

    next {
        var m: MessageType;
        d := R.ack();
        R.recv(c);
        c := S.send(m, d);
    }

    procedure @system() {
        var m: MessageType;
        
        while (true) {
            havoc m;
            S.waitForAck();
            R.processMessage();
        }
    }
}

module Sender {
    var curr_message: MessageType;
    var waiting_for_ack: boolean;
    var control_bit: boolean;

    init {
        waiting_for_ack := false;
        control_bit := false;
    }

    procedure send(m: MessageType, ack_received: boolean) returns (c: [MessageType] boolean) {
        c := [msg: MessageType] false; // Creates an array where all elements are initially set to false
        if (!waiting_for_ack || ack_received) {
            curr_message := m;
            control_bit := !control_bit;
            waiting_for_ack := true;
            c[curr_message] := true; // Attempt to send the message
        }
        return c;
    }

    procedure waitForAck() {
        // Simulation for possible ack handling and timeout
        if (true) { // Non-deterministic choice (as if modelling a timeout) assumed always true for example
            waiting_for_ack := true;
        } else {
            waiting_for_ack := false;
        }
    }

    function ack() returns (b: boolean) {
        return control_bit;
    }
}

module Receiver {
    var received_control_bit: boolean;

    init {
        received_control_bit := false;
    }

    procedure recv(c: [MessageType] boolean) {
        var m: MessageType;
        if (c[m]) { // Check if the message exists on the channel
            received_control_bit := !received_control_bit;
        }
    }

    function ack() returns (b: boolean) {
        return received_control_bit;
    }

    procedure processMessage() {
        // Processes that the receiver might perform when processing the message
    }
}
```