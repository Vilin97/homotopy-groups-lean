# Audited Lean 4 formalizations

[`formalizations.json`](formalizations.json) is the dated, machine-readable
inventory behind the website's purple overlay.  The maintained proof sets and
the displayed overlay are Lean 4 only.  Each positive entry has a source path,
model qualification, trust status, and license; public dependencies are
commit-pinned.

The repository includes a sorry-free proof that `pi_k(S^n)` vanishes below the
sphere dimension.  Its minimal twelve-module closure is vendored under
[`examples/submissions/sphere_lower_homotopy_subsingleton`](../examples/submissions/sphere_lower_homotopy_subsingleton/)
and is evaluated against the benchmark-owned statement.  This result does not
occupy a square in the displayed `(n,k)` lattice, because that lattice begins at
`pi_n(S^n)` and moves upward.

The metric-circle submissions close the model gap for the first row of the
lattice by constructing the homeomorphism from Mathlib's complex `Circle` to
the benchmark's `SphereSpace 1`.  One proof transports the exponential
covering computation to show `pi_1(S^1) = Z`; the earlier general proof ports
covering invariance to show `pi_m(S^1) = 0` for every `m >= 2`.  The higher
row is one general formalized result.  Its named degree corollaries are
conveniences and are not counted separately.

## Twenty additional Lean 4 results

`maintained_lean4_twenty_result_set` records exactly twenty mathematically
distinct Lean 4 declarations in
[`Lean4TwentyResults.lean`](../examples/submissions/sphere_lower_homotopy_subsingleton/Submission/Lean4TwentyResults.lean).
They cover retract injectivity, section surjectivity, strict equivalences,
vanishing transfer, homeomorphism and pointed-homotopy invariance, product
triviality, contractible factors, products of fundamental groups and path
components, basepoint independence, higher-group commutativity, covering-map
injectivity, and exact metric-circle computations at arbitrary basepoints.
Numerical specializations, displayed cells, and aliases are not counted.

The maintained Lean 4 closure now also contains the path fibration, the
degree-one Hurewicz theorem, the needed Mayer--Vietoris and Wang machinery, and
the computation `H_1(ΩS²) = Z`.  Their composition proves `pi_2(S^2) = Z` in
the exact metric-sphere model and adds `(n,k)=(2,0)` to the overlay.  The honest
Lean 4 overlay therefore has 92 cells: the complete 91-cell `n=1` row and this
first diagonal cell.

Higher diagonal and stable sphere stems still require additional
Freudenthal, higher-Hurewicz, and Hopf-fibration infrastructure.  Incomplete
attempts do not color cells.

The maintained ten-result set is recorded explicitly in
`maintained_independent_result_set`.  Besides the metric-circle computation it
contains nine mathematically distinct structural theorems: the `pi_0` and
`pi_1` comparisons, change of basepoint, homotopy invariance, the binary product
formula, functoriality of induced maps, pointed-homotopy invariance,
covering-space invariance, and contractible-space vanishing.  Only the
metric-circle theorem colors lattice cells; the other nine are reusable
foundations and the inventory says so rather than presenting them as new sphere
computations.

The purple overlay records Lean 4 proofs only and never promotes the underlying
mathematical evidence class.  It does not propagate a stable representative
across an entire diagonal without formal suspension equivalences.

Deleted-source and incomplete attempts remain in `qualified_records` so the
negative audit is reproducible.  They do not color cells.

Three additional public, sorry-free `pi_1(Circle)` submissions are retained as
commit-pinned links in `related_public_proofs`. Their audited snapshots do not
contain an explicit source license, so this repository does not copy them.
