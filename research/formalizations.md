# Audited formalizations

[`formalizations.json`](formalizations.json) is the dated, machine-readable
inventory behind the website's purple overlay.  The audit covers the public
Lean/Mathlib ecosystem, LeanEval submissions, TauCeti, GroundZero, Lean's
historical HoTT library, and the official Cubical Agda library.  Each positive
entry has a source path, model qualification, trust status, and license; public
dependencies are commit-pinned.

The strongest current-model result imported into this repository is the
sorry-free proof that `pi_k(S^n)` vanishes below the sphere dimension.  Its
minimal twelve-module closure is vendored under
[`examples/submissions/sphere_lower_homotopy_subsingleton`](../examples/submissions/sphere_lower_homotopy_subsingleton/)
and is evaluated against the benchmark-owned statement.  This result does not
occupy a square in the displayed `(n,k)` lattice, because that lattice begins at
`pi_n(S^n)` and moves upward.

The metric-circle submissions close the model gap for the first row of the
lattice by constructing the homeomorphism from Mathlib's complex `Circle` to
the benchmark's `SphereSpace 1`.  The new proof transports the exponential
covering computation to show `pi_1(S^1) = Z`; the earlier general proof ports
covering invariance to show `pi_m(S^1) = 0` for every `m >= 2`.  The higher row
is one general formalized result.  Its named degree corollaries are conveniences
and are not counted separately.

## The second ten-result batch

`maintained_second_result_set` records exactly ten mathematically distinct
declarations.  It does not count numerical instances or displayed cells.  One
is the new exact-model Lean theorem for `pi_1(S^1)`.  Nine are Cubical Agda
sphere results: the diagonal group, its identity generator, its cohomological
identification, `pi_3(S^2)`, `pi_4(S^3)`, first-stem suspension, the higher Hopf
sphere equivalence, `pi_4(S^2)`, and the full first stable stem.

The companion source
[`formalizations/cubical/SecondBatch.agda`](../formalizations/cubical/SecondBatch.agda)
adds the transfer and stability derivations.  The reproducible checker uses
digest-pinned Agda 2.8.0 and
[`agda/cubical`](https://github.com/agda/cubical) commit
`92166033326aa59800a580b428125f3c654b5e45`, then type-checks the companion with
`--safe`.  The checked proof overlay now occupies 274 displayed cells: the full
`n=1` row, all diagonal cells, the complete first stem, and `pi_4(S^2)`.

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
can record a source-auditable formalization in an exact metric model or in a
synthetic higher-inductive sphere model.  The detail pane always states the
proof assistant and model.  It never promotes the underlying mathematical
evidence class.  The first-stem cells are propagated only because
`SecondBatch.firstStemSuspIso` supplies the formal suspension isomorphisms.

Deleted-source and incomplete attempts remain in `qualified_records` so the
negative audit is reproducible.  They do not color cells.

Three additional public, sorry-free `pi_1(Circle)` submissions are retained as
commit-pinned links in `related_public_proofs`. Their audited snapshots do not
contain an explicit source license, so this repository does not copy them.
