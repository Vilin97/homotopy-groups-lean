# Higher homotopy groups are commutative

This maintained submission solves `higher_homotopy_mul_comm`: for every
`n : ℕ`, multiplication on Mathlib's cubical model of
`HomotopyGroup.Pi (n + 2) X x` is commutative.

The proof invokes `mul_comm` from the `CommGroup` instance that Mathlib builds
for generalized-loop index types with at least two elements.  Mathlib constructs
that instance via the Eckmann–Hilton argument in
[`Mathlib/Topology/Homotopy/HomotopyGroup.lean`](https://github.com/leanprover-community/mathlib4/blob/905b95818eb32af7874a58b427f50c1711a5e96c/Mathlib/Topology/Homotopy/HomotopyGroup.lean#L596-L610).
The benchmark pins that exact Mathlib commit,
`905b95818eb32af7874a58b427f50c1711a5e96c`.

For the underlying mathematical result, see Allen Hatcher,
[*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
§4.1, p. 340, where `πₙ(X, x₀)` is proved abelian for `n ≥ 2`.

The hosted evaluator should be given this directory as the submission path. It
copies only `Submission.lean` into a pristine generated challenge; this fixture
has no private helper modules or replacement build configuration.
