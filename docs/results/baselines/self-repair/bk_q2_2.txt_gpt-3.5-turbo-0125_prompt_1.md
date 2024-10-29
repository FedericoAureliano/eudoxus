Write UCLID5 code to complete the following task.

> We are given three (primitive) processes P1,P2, and P3 with shared integer variable x. The program of each process is as follows: for x = 1,...,10 do LOAD(x); INC(x); STORE(x); od That is, each process executes ten times the assignment x:=x+1. The assignment x := x+1 is realized using the three actions LOAD(x), INC(x) and STORE(x). Consider now the parallel program: x := 0; P1 || P2 || P3 Build a model of the parallel program. Write a property that checks if P has an execution that halts with the terminal value x=2. Use the variable name x.

Reply with your UCLID5 code inside one unique code block.

I can definitely do that! Here is the UCLID5 code:
```
