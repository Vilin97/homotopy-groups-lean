# Lower homotopy groups of spheres

This submission proves `sphere_lower_homotopy_subsingleton`: for `k < n`, the
Mathlib homotopy group `π_k(S^n)` of the unit metric sphere in
`EuclideanSpace ℝ (Fin (n + 1))` is subsingleton.

The proof uses piecewise-affine approximation on a cubical grid. General
position supplies a point missed by the approximating map, so the map factors
up to homotopy through the complement of that point; the sphere complement is
contractible. The source closure consists of exactly twelve modules below
`Submission/`.

The proof and modules are adapted from
[`Vilin97/lean-eval-pi-succ-sphere`](https://github.com/Vilin97/lean-eval-pi-succ-sphere/tree/1be6cb9b42874415a34defee070f4aa07d6e3193/Submission)
at commit `1be6cb9b42874415a34defee070f4aa07d6e3193`. Every copied module retains its
Apache-2.0 header; the two homotopy-invariance modules also retain their Tau
Ceti attribution.

The hosted evaluator should be given this directory as the submission path. It
copies `Submission.lean` and all Lean modules below `Submission/` into a
pristine generated challenge before running the comparator and independent
kernel.
