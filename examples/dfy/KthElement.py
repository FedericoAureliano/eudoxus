from typing import List

import dafnypy


@dafnypy.verify
def KthElement(arr: List[int], k: int) -> int:
    # Precondition: requires statements for precondition
    dafnypy.requires(1 <= k)
    dafnypy.requires(k <= len(arr))

    # Main function body
    result = arr[k - 1]

    # Post-condition: ensures statements for post-condition
    dafnypy.ensures(result == arr[k - 1])
    return result


print(KthElement([10, 3, 5, 2], 1))
KthElement([10, 3, 5, 2], 0)
