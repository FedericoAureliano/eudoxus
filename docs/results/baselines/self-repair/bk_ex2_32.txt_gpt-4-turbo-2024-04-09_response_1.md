```uclid
module main {
    type MessageType;
    instance S: Sender;
    instance R: Receiver;

    // Channel c for sender to receiver with potential loss of data
    // Channel d is perfect
    var c: [MessageType] boolean;
    var d: boolean;

    init {
        d = false;
        forall (m: MessageType) :: c[m] = false;
    }

    next {
        d = R.ack();
        R.recv(c);
        c = S.send(m, d);
    }

    procedure @system() {
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
        waiting_for_ack = false;
        control_bit = false;
    }

    procedure send(m: MessageType, ack_received: boolean) returns (c: [MessageType] boolean) {
        if (!waiting_for_ack || ack_received) {
            curr_message = m;
            control_bit = !control_bit;
            waiting_for_ack = true;
        }
        c[curr_message] = true;                           // Attempt to send the message
        return c;
    }

    procedure waitForAck() {
        // Introducing non-determinism to model potential timeout
        if (*) { // Timeout can occur
            waiting_for_ack = true;
        } else if (ack) { // Ack received
            waiting_for_ack = false;
        }
    }

    function ack() returns (b: boolean) {
        return control_bit;
    }
}

module Receiver {
    var received_control_bit: boolean;

    init {
        received_control_bit = false;
    }

    procedure recv(c: [MessageType] boolean) {
        var m: MessageType;
        if (c[m]) { // Check if the message is in the channel
            received_control_bit = !received_control_bit;
        }
    }

    function ack() returns (b: boolean) {
        return received_control_bit;
    }

    procedure processMessage() {
        // Procedures that receiver R might perform when processing the message
    }
}
```
This UCLID5 model demonstrates the setup and operation for the sender (S) and receiver (R), including the inclusion of unreliable channel `c` and the reliable channel `d`. The send-and-wait mechanism is modeled along with retransmission in case of timeout using nondeterministic choice (`*`) in `waitForAck`. Channels are modelled using arrays, marking them with `true` if a message occupies that space in the buffer. Receiver processes messages and sends acknowledgments via a perfect channel. Sender changes the control bit every successful transmission, expecting the acknowledgment with the new control bit value.