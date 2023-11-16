Plan: write regression tests for UCLID5 features with the following template

```
// Purpose: {the purpose of the test}
// Description: {what the code is doing}
// Expectation: {the expected result of executing the test}
// Validation: {how can we validate that the test is useful?}

{uclid code}
```

Note: Tests should aim for semantic errors (i.e., type checking and beyond) not parsing errors (e.g., mismatched parenthesis). Note that test 6 is for a parsing error.

Tests that might actually be bugs: 6.ucl, 9.ucl, 14.ucl.