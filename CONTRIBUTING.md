# Contributing

## Benchmark statements

Keep declarations mathematical, explicit, and independently reviewable. Each
new `@[eval_problem]` declaration must have one matching manifest. Include a
primary source, explain any formalization gap in `notes`, and never label a
statement “known” solely because it appears in an informal table.

Run before submitting:

```bash
lake exe homotopy-groups-lean validate-manifest
lake exe homotopy-groups-lean check-problem-build
lake exe homotopy-groups-lean generate --check
lake exe homotopy-groups-lean check-generated-builds
```

Expected `declaration uses 'sorry'` warnings are allowed for unsolved benchmark
holes. Other Lean warnings should be fixed.

## Solutions

Do not edit trusted challenge material. Solver changes are limited to
`Submission.lean`, Lean files under `Submission/`, and the narrow documentation
and license additions accepted by `validate-submission`. A leaderboard result
must include the benchmark commit, problem id, trusted-workspace fingerprint,
exact toolchain, comparator verdict, and enough provenance to reproduce the run.

Hosted submissions must point to a public GitHub repository and immutable commit.
Only proof files are imported. A submission issue is a request to evaluate that
specific commit, not authorization to merge or execute the rest of its repository.

## Catalog and website data

Use stable ids across Lean, manifests, tracker data, and results. Preserve
citations and distinguish these statuses: formalized upstream, benchmark solved,
benchmark open, and mathematically open. Website changes must not silently
override Lean or manifest metadata.
