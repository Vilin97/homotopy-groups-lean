# Audited Lean formalizations

[`formalizations.json`](formalizations.json) is the dated, machine-readable
inventory behind the website's purple overlay.  The audit searched the public
Lean/Mathlib ecosystem, LeanEval submissions, nearby local checkouts, TauCeti,
GroundZero, and Lean's historical HoTT library.  Each positive entry has a
commit, source path, model qualification, and license.

The strongest current-model result imported into this repository is the
sorry-free proof that `pi_k(S^n)` vanishes below the sphere dimension.  Its
minimal twelve-module closure is vendored under
[`examples/submissions/sphere_lower_homotopy_subsingleton`](../examples/submissions/sphere_lower_homotopy_subsingleton/)
and is evaluated against the benchmark-owned statement.  This result does not
occupy a square in the displayed `(n,k)` lattice, because that lattice begins at
`pi_n(S^n)` and moves upward.

The metric-circle submission closes the model gap for the first row of the
lattice.  It constructs the homeomorphism from Mathlib's complex `Circle` to
the benchmark's `SphereSpace 1`, ports the covering-space isomorphism on higher
homotopy groups to the pinned toolchain, and proves `pi_m(S^1) = 0` for every
`m >= 2`.  This entire row is one general formalized result.  Its named degree
corollaries are conveniences and are not counted as separate results.

The maintained ten-result set is recorded explicitly in
`maintained_independent_result_set`.  Besides the metric-circle computation it
contains nine mathematically distinct structural theorems: the `pi_0` and
`pi_1` comparisons, change of basepoint, homotopy invariance, the binary product
formula, functoriality of induced maps, pointed-homotopy invariance,
covering-space invariance, and contractible-space vanishing.  Only the
metric-circle theorem colors lattice cells; the other nine are reusable
foundations and the inventory says so rather than presenting them as new sphere
computations.

The purple overlay is deliberately broader than “same Lean declaration”: it
can record a source-auditable formalization in a historically important or
equivalent circle/synthetic sphere model.  The detail pane always states which
model and Lean generation was used.  It never promotes the underlying
mathematical evidence class and never propagates a stable representative across
an entire diagonal without formal suspension equivalences.

Deleted-source and incomplete attempts remain in `qualified_records` so the
negative audit is reproducible.  They do not color cells.

Three additional public, sorry-free `pi_1(Circle)` submissions are retained as
commit-pinned links in `related_public_proofs`. Their audited snapshots do not
contain an explicit source license, so this repository does not copy them.
