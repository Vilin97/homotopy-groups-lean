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
