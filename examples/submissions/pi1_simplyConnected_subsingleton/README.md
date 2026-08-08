# Simply connected spaces have trivial `π₁`

This submission solves `pi1_simplyConnected_subsingleton`. Mathlib's
`SimplyConnectedSpace` API makes `FundamentalGroup X x` a subsingleton, while
`HomotopyGroup.pi1MulEquivFundamentalGroup` identifies it multiplicatively with
`HomotopyGroup.Pi 1 X x`. Injectivity transports triviality across that
equivalence.

The proof uses only pinned Mathlib declarations and the benchmark-permitted
axioms. The mathematical reference attached to the problem is Hatcher,
*Algebraic Topology*.
