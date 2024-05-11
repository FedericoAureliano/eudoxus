# flake8: noqa
def find_max_length_lists(lists):
    # Initialize variables to keep track of the max length and corresponding lists
    max_length = -1
    max_length_lists = []

    i = 0
    # Loop through each list
    while i < len(lists):
        sublist = lists[i]
        # Check if the current sublist's length is greater than the known max length
        if len(sublist) > max_length:
            max_length = len(sublist)
            # If a new max length is found, reset the list of max length lists
            max_length_lists = [sublist]
        elif len(sublist) == max_length:
            # If the current sublist's length matches the known max length, add it to our list
            max_length_lists.append(sublist)
        i += 1

    return max_length_lists


# Example usage
lists_of_lists = [[1, 2, 3], [4, 5], [6, 7, 8, 9], [10], [11, 12]]
max_lists = find_max_length_lists(lists_of_lists)
print("List(s) with maximum length:", max_lists)
