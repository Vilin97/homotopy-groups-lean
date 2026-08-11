# Higher homotopy groups of the metric circle

This maintained submission solves
`sphere_one_higher_homotopy_subsingleton` for the benchmark's exact
`SphereSpace 1` model.  It therefore proves every group
`pi_(k+2)(S^1)` trivial, not merely an analogous statement for `Circle` or
`AddCircle`.

The proof has three geometric steps:

1. the quotient map `Real -> AddCircle 1` is a covering map;
2. covering maps induce isomorphisms on homotopy groups in dimensions at
   least two, while every homotopy group of `Real` is trivial by affine
   contraction; and
3. `Complex.orthonormalBasisOneI.repr` restricts to an explicit homeomorphism
   from Mathlib's complex unit circle to the unit sphere in
   `EuclideanSpace Real (Fin 2)`.

The covering-space portion is adapted under Apache-2.0 from
[TauCeti](https://github.com/TauCetiProject/TauCeti/blob/2b5d1fc89767051f490d5b4f00e76a4cdbd92876/TauCeti/AlgebraicTopology/UniversalCover/Circle/HigherHomotopy.lean).
This port targets the benchmark's pinned Lean 4.32.2 and Mathlib commit.

Ten convenience corollaries expose the first ten direct-model lattice cells:
`pi2_sphere_one_subsingleton` through `pi11_sphere_one_subsingleton`, at
coordinates `(n,k) = (1,1)` through `(1,10)`.  The general benchmark theorem
continues to cover the rest of the row.  These specializations are not counted
as ten results: the higher-vanishing theorem for the metric circle counts once.

For the classical mathematics, see Allen Hatcher,
[*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
Proposition 4.1 and the discussion of higher homotopy groups of covering
spaces.
