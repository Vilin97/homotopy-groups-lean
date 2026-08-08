# The fundamental group of an H-space is abelian

This submission solves `pi1_hSpace_mul_comm` without assuming commutativity.
It defines pointwise H-space multiplication on based paths and descends it
through path homotopy to the fundamental group. The two H-space unit homotopies
make this operation unital, while pointwise multiplication strictly
interchanges with path concatenation. Mathlib's abstract Eckmann--Hilton theorem
then proves that loop concatenation is commutative. Finally, the result is
transported to `HomotopyGroup.Pi 1` along
`HomotopyGroup.pi1MulEquivFundamentalGroup`.

The mathematical source attached to the benchmark is:

- I. M. James, *Reduced product spaces*, Annals of Mathematics 62 (1955),
  DOI [10.2307/1969485](https://doi.org/10.2307/1969485).

All helper definitions are local to `Submission.lean`; the proof uses only the
pinned Mathlib and the benchmark-permitted axioms.
