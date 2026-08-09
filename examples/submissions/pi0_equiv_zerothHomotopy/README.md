# Zeroth homotopy groups are path components

This maintained submission solves `pi0_equiv_zerothHomotopy`. It packages
Mathlib's native equivalence
`HomotopyGroup.pi0EquivZerothHomotopy` in the benchmark theorem's `Nonempty`
wrapper.

The underlying construction identifies zero-dimensional generalized loops
with points and carries generalized-loop homotopies to paths. The proof uses
only the pinned Mathlib declaration and the benchmark-permitted axioms.
