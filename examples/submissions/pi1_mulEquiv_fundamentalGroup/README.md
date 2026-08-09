# First homotopy groups are fundamental groups

This maintained submission solves `pi1_mulEquiv_fundamentalGroup`. It packages
Mathlib's native multiplicative equivalence
`HomotopyGroup.pi1MulEquivFundamentalGroup` in the benchmark theorem's
`Nonempty` wrapper.

The upstream construction identifies one-dimensional generalized loops with
based paths modulo homotopy and proves that the identification preserves loop
composition. The proof uses only the pinned Mathlib declaration and the
benchmark-permitted axioms.
