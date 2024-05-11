from typing import List

import dafnypy

# flake8: noqa


@dafnypy.verify
def find_peak_indices(mountain: List[int]) -> List[int]:
    # Precondition: the mountain list must not be empty and should have at least 3 elements for a peak to exist
    dafnypy.requires(len(mountain) >= 3)

    peaks = []

    # Main function body
    for i in range(1, len(mountain) - 1):
        # Loop Invariant: At the start of each iteration, 'peaks' contains all valid peak indices found in mountain[0..i]
        dafnypy.invariant(
            all(
                mountain[peak] > mountain[peak - 1]
                and mountain[peak] > mountain[peak + 1]
                for peak in peaks
            )
        )
        dafnypy.invariant(i <= len(mountain) - 1)
        dafnypy.invariant(len(peaks) <= i)

        if mountain[i] > mountain[i - 1] and mountain[i] > mountain[i + 1]:
            peaks.append(i)

    result = peaks

    # Post-condition: ensures that all elements in 'result' are valid peak indices
    dafnypy.ensures(
        all(
            mountain[result[i]] > mountain[result[i] - 1]
            and mountain[result[i]] > mountain[result[i] + 1]
            for i in range(len(result))
        )
    )
    return result


print(find_peak_indices([1, 2, 3, 4, 5, 4, 3, 2, 1]))
find_peak_indices([1, 5])
