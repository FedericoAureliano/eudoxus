from typing import List

import dafnypy


# flake8: noqa
@dafnypy.verify
def count_true_booleans(boolean_array: List[bool]) -> int:
    # No explicit requires as this function should work for any input list of boolean values

    # Initialize a counter for True values
    count = 0
    # Initialize the starting index for the while loop
    index = 0

    # Main function body
    while index < len(boolean_array):
        dafnypy.invariant(
            index <= len(boolean_array)
        )  # ensures index does not exceed list bounds
        dafnypy.invariant(0 <= index)  # ensures index is non-negative
        # This invariant establishes that for the portion of the list we've seen so far,
        # `count` is exactly the number of True values.
        dafnypy.invariant(count == sum(1 for x in boolean_array[:index] if x == True))
        dafnypy.decreases(
            len(boolean_array) - index
        )  # ensures progress towards loop termination

        # Check if the current element is True
        if boolean_array[index] == True:
            count += 1  # Increment the counter
        index += 1  # Move to the next element

    # Post-condition: The count must equal the total number of True values in the boolean array
    dafnypy.ensures(count == sum(1 for x in boolean_array if x == True))

    return count


count_true_booleans([True, False, True, True, False, False, True])
