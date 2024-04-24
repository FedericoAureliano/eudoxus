% Automatically Repairing a Program Using a QF_ADT Solver
% Federico Mora and Adwait Godbole
% April 24, 2024

# The Abstract Syntax Tree

## Meta Definitions

```ocaml
type symbol
    (* in reality an uninterpreted sort *)
    = string

type natural =
  | Zero
  | Succ of {pred: natural}

type boolean =
  | True
  | False

type 'a list =
  | Empty
  | Cons of {head: 'a; tail: 'a list}

(* OCaml doesn't need named tuples, but SMTLIB does *)
type ('a, 'b) pair = Pair of {fst: 'a; snd: 'b}
type 'a single = Single of {fst: 'a}
```

## Sorts and Terms

```ocaml
type sort =
  | BooleanSort
  | IntegerSort
  | BitVectorSort of {width: natural}
  | ArraySort of {index: sort; element: sort}
  | EnumSort of {variants: symbol list}
  | RecordSort of {fields: (symbol, sort) pair list}

type term =
  | BooleanVal of {value: boolean}
  | IntegerVal of {sign: boolean; value: natural}
  | BitVectorVal of {width: natural; value: natural}
  | ArrayVal of {index_sort: sort; element_sort: sort; value: term}
  | EnumVal of {variant: symbol}
  | RecordVal of {fields: (symbol, sort) pair list}
  | Variable of {name: symbol}
  | Not of term single
  | And of (term, term) pair
  | Or of (term, term) pair
	(* ... *)
  | Add of (term, term) pair
  | Mul of (term, term) pair
	(* ... *)
  | IfThenElse of {condition: term; then_term: term; else_term: term}
```

## Term -> Sort
```ocaml
let sort_of: term -> sort
    (* in reality an uninterpreted function *)
    = fun x -> BooleanSort
```

## Example Encoding, Input
```python
class M(Module):
    def locals(self):
        self.x = BitVector(8)

    def init(self):
        self.x = self.x + 1
```

## Example Encoding, Annotated
```python
class M(Module):
    def locals(self):
        self.x = BitVector(8)
        # let x: term
        # let s: sort
        # hard-assert get_sort(x) == s
        # soft-assert s == BitVectorSort(width=8)

    def init(self):
        self.x = self.x + 1
        # let t: term
        # soft-assert t == 1
        # hard-assert get_sort(1) == IntegerSort

        # hard-assert get_sort(x) == get_sort(t)

        # hard-assert get_sort(x) == get_sort(Add(x, t))
        # hard-assert get_sort(Add(x, t)) == get_sort(x)
        # hard-assert get_sort(Add(x, t)) == get_sort(t)
```

## Example Encoding, Logic Only
```ocaml
let x: term
let s: sort
get_sort(x) == s
s == BitVectorSort(width=8)         (* soft *)
let t: term
t == 1                              (* soft *)
get_sort(1) == IntegerSort
get_sort(x) == get_sort(t)
get_sort(x) == get_sort(Add(x, t))
get_sort(Add(x, t)) == get_sort(x)
get_sort(Add(x, t)) == get_sort(t)
```

## Example Encoding, Conflict
```ocaml
IntegerSort == get_sort(1)
get_sort(1) == get_sort(t)      (* soft *)
get_sort(t) == get_sort(x)
get_sort(x) == s
s == BitVectorSort(width=8)     (* soft *)
```

## Example Encoding, MAX-SAT
```ocaml
IntegerSort == get_sort(1)
get_sort(1) == get_sort(t)
get_sort(t) == get_sort(x)
get_sort(x) == s
(* s == BitVectorSort(width=8) *)
```

## Example Encoding, Model
```ocaml
IntegerSort == get_sort(1)
get_sort(1) == get_sort(t)
get_sort(t) == get_sort(x)
get_sort(x) == s
(* s == IntegerSort *)
```

## Example Encoding, Output
```python
class M(Module):
    def locals(self):
        self.x = int # used to be BitVector(8)

    def init(self):
        self.x = self.x + 1
```
