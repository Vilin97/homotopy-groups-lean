# Benchmark design

## Sources of truth

The trusted Lean declaration defines what must be proved. Its TOML manifest
provides stable identity, display metadata, provenance, and benchmark status.
Generated workspaces are deterministic projections of those two sources. The
website and leaderboard may index them, but must not redefine a goal.

```text
HomotopyGroups/*.lean + manifests/problems/*.toml
                         |
                         v
                  generator + inventory
                         |
                         v
                 generated/<problem-id>/
                         |
                         v
              comparator + nanoda verdict
                         |
                         v
                tracker / leaderboard
```

## Catalog semantics

The catalog is meant to grow toward the known literature, but “all known
results” is an evolving research target rather than a finite completeness
claim. Every row should identify its mathematical source and formalization
status. Open conjectures must be labeled separately from established theorems
whose Lean proofs are missing.

A useful problem is mathematically meaningful, accurately scoped, expressible
against the pinned Mathlib API, and stable enough that comparator can isolate
participant-owned declarations. Prerequisite definitions may be trusted shared
infrastructure; benchmark holes are exactly the names listed in `holes`.

## Verdict and leaderboard invariant

A leaderboard success is valid only for a tuple of benchmark commit, problem id,
the deterministic fingerprint of its trusted generated workspace, submission
identity, pinned toolchain, and successful comparator-plus-nanoda verdict.
Displayed aggregate scores must be derivable from retained per-problem verdicts.
A retained verdict becomes historical, and stops contributing to current totals,
when that problem fingerprint or evaluator identity changes. Re-running the same
tuple should reproduce the result.
