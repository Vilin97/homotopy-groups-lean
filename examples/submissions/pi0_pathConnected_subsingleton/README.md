# Path-connected spaces have trivial `π₀`

This submission solves `pi0_pathConnected_subsingleton`. Mathlib gives an
equivalence from `HomotopyGroup.Pi 0 X x` to `ZerothHomotopy X`; path
connectedness supplies the subsingleton structure on the latter. Injectivity of
the equivalence transports it back to `π₀`.

The proof uses only pinned Mathlib declarations and the benchmark-permitted
axioms. The mathematical reference attached to the problem is Hatcher,
*Algebraic Topology*.
