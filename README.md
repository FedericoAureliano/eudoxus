# uclid-lm-ir

Goal: when we create a new feature in UCLID5 or we find a bug in an existing feature, we want to generate regression tests for it. For example, we know the corner cases of the spec for algebraic data types but it is tedious to write the tests. Can we describe them in natural language and get an llm to help us generate the tests?

Main insight: meet the llm hallway by designing a Python API for it to use as an intermediate representation.

Data: natural language description of all existing regression tests

Method for getting data:
- Describe what the test is doing and what it is testing. One-ish sentence each.

Method for getting intermediate representation:
1. ask llm to generate Python code using a uclid5 api that doesn’t exist yet for each of the training regression tests.
1. Create Python API that will make as many of those outputs be correct

Optimizations: add prompting, feedback loops, etc. to get even better results on training set.

Evaluation:
1. Give the test set regression test descriptions
2. Manually check that the outputs test the desired thing? Or could do coverage metrics? Or mutation testing on Uclid5 itself (insert a bug in the code that the test is supposed to be testing and see if the test catches it)?