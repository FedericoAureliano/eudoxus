TODO
--------
- [x] support `+=`
- [x] type checking for lists
- [x] support `len` function natively
- [x] support `sum` function natively
- [x] support DeclAssignments, typed assignments probably mean decl
- [x] support `append`
- [x] support `in`
- [x] identifier `array1` is not allowed because it has the word array in it
- [x] support untyped empty list
    - e.g. `variable = []`

- [x] `set`
    - supported in cases where it's just an identifier under

- [ ] support list comprehension
    - e.g. `all(item in array2 for item in shared_elements)`
    - e.g. `dafnypy.ensures(count == sum(1 for x in boolean_array if x == True))`
- [ ] List comprehension plus set
    - `dafnypy.invariant(set(odd_numbers) == set(num for num in numbers[:index] if num % 2 != 0))
- [ ] generics e.g. `T = TypeVar('T')`
