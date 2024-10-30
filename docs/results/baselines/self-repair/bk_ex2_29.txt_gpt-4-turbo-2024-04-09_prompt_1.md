Write UCLID5 code to complete the following task.

> Consider a (strongly simplified) booking system at a cashier of a supermarket. The system consists of three processes: the bar code reader BCR, the actual booking program BP, and the printer Printer. The bar code reader reads a bar code and communicates the data of the just scanned product to the booking program. On receiving such data, the booking program transmits the price of the article to the printer that prints the article Id together with the price on the receipt. The interactions between the bar code reader and the booking program, and between the booking program and the printer is performed by handshaking. Each process consist of just two states, named 0 and 1. BCR transitions from state 0 to state 1 when a bar code is scanned, and from state 1 to state 0 when the data is sent to BP. BP transitions from state 0 to state 1 when it receives data from BCR, and from state 1 to state 0 when it sends the print command to the printer Printer transitions from state 0 to state 1 when the print code is sent by BP, and from state 1 to state 0 when the article is printed.  The complete system is given by: BCR || BP || Printer. Model this system. Use the variable names BCR_state, BP_state and Printer_state.

Reply with your UCLID5 code inside one unique code block.

I can definitely do that! Here is the UCLID5 code:
```