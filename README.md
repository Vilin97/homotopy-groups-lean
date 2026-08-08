# Homotopy Groups in Lean

A comparator-gated benchmark for formalizing the known theory and computations
of homotopy groups, recording open problems precisely, and evaluating Lean
solutions reproducibly. The catalog distinguishes results already proved in
Mathlib, benchmark statements that still contain `sorry`, and genuinely open
mathematical conjectures; a statement's presence is not a claim that it has
already been formalized.

The [companion site](https://vilin97.github.io/homotopy-groups-lean/)
presents the problem tracker and leaderboard; its source lives in
[`website/`](website/). The Lean source and per-problem manifests are the
benchmark's authoritative data.

The corpus contains **126 Lean statements**: every additive stable stem from 0
through 90 (87 exact values and the complete published alternatives in stems
84, 85, 86, and 90), 33 foundational/unstable/advanced results, and two
concrete open conjectures. Seven open-conjecture families are source-tracked in
[`research/open-problems.json`](research/open-problems.json); five whose required
foundations do not yet exist in Mathlib are recorded as blocked instead of being
weakened into placeholder propositions.

The audited 92 by 91 knowledge lattice is specified in
[`research/lattice-coverage.json`](research/lattice-coverage.json). The attached
[literature review](website/public/reports/homotopy-groups-of-spheres-literature-review.pdf),
its [correction log](research/literature-review-audit.md), and the regenerated
[CSV/BibTeX companions](research/report-data/) distinguish exact integral
values, published alternatives, 2-primary-only computations, and a disputed
33-stem entry. The independent purple proof overlay comes from the dated,
source-auditable [`formalizations.json`](research/formalizations.json) inventory.

## Reproducible environment

The root project is pinned to:

- Lean `v4.32.2` (`leanprover/lean4:v4.32.2`)
- Mathlib commit `905b95818eb32af7874a58b427f50c1711a5e96c`
- `lean4-cli` commit `88679d088c9720c27ebdf2ba4dafe17341747f94`

```bash
lake exe cache get
lake build
lake exe homotopy-groups-lean --help
```

The bare cache command above is a local-development convenience. Hosted
evaluation clears cache URL overrides and forces Mathlib's high-trust `master`
container followed only by its read-only legacy mirror; see
[SECURITY.md](SECURITY.md#immutable-dependency-pins).

## How the benchmark is gated

1. A trusted declaration under `HomotopyGroups/` is marked
   `@[eval_problem]` and registered in exactly one
   `manifests/problems/<id>.toml` file.
2. `generate` extracts the declaration and its trusted local dependencies into
   an isolated Lake project at `generated/<id>/`.
3. Solvers change only `Submission.lean` and Lean modules below `Submission/`.
4. `lake test` invokes comparator. The committed `WorkspaceTest.lean` forces
   comparator to replay the candidate through nanoda's independent kernel.
5. A result counts as solved only when this gated test exits successfully.

`Solution.lean`, `Challenge.lean`, `config.json`, and the generated Lake files
are trusted benchmark material, not solver-owned input.

## Problem-author workflow

Add the Lean statement and manifest together. A minimal entry is documented in
[`manifests/README.md`](manifests/README.md).

```bash
lake exe homotopy-groups-lean validate-manifest
lake exe homotopy-groups-lean check-problem-build
lake exe homotopy-groups-lean generate --problem <problem-id>
lake exe homotopy-groups-lean check-generated-builds --problem <problem-id>
```

Every instance hole must have an explicit stable name. Multi-hole problems list
all theorem, definition, and instance names in `holes`. Citations should use a
stable DOI, archival URL, or complete bibliographic reference, and the notes
must say when the Lean statement is weaker, conditional, or otherwise differs
from the cited mathematics.

## Solver workflow

```bash
lake exe homotopy-groups-lean start-problem <problem-id>
cd workspaces/<problem-id>
lake update
# edit Submission.lean and/or Submission/*.lean
lake test
```

From the repository root, score one or more local attempts with:

```bash
lake exe homotopy-groups-lean run-eval --problem <problem-id>
lake exe homotopy-groups-lean run-eval --json
```

The scorer prefers `workspaces/<id>/` and otherwise examines the pristine
generated workspace. Validate submission paths with:

```bash
lake exe homotopy-groups-lean validate-submission \
  --file generated/<problem-id>/Submission.lean
```

## Hosted submission flow

Open the [submission Issue Form](https://github.com/Vilin97/homotopy-groups-lean/issues/new?template=submit.yml)
with one problem id, a public GitHub repository, an exact 40-character commit
SHA, and the relative directory containing `Submission.lean`. The workflow:

1. authenticates the repository metadata lookup, then fetches and inspects the
   exact commit and requested proof path before provisioning evaluator tools;
2. checks out a benchmark-owned pristine workspace and copies only
   `Submission.lean` and `.lean` files below `Submission/` from the pinned public
   commit;
3. runs comparator in landrun with the permitted-axiom closure, Lean's kernel,
   and nanoda's independent kernel;
4. binds the verdict to the pristine problem workspace's deterministic fingerprint;
5. passes a source-free, SHA-digested verdict to a separate write-capable job;
6. validates the current fingerprint and exact evaluator pins, appends an immutable
   JSON record, then strictly revalidates every retained record before deriving
   the public leaderboard from current results only.

The evaluator job has `contents: read` only and receives no repository-write or
issue-write token. Submitted lakefiles, toolchains, challenges, solution bridges,
configs, workflows, symlinks, and non-Lean files are ignored or rejected.

The maintained positive fixture is
[`examples/submissions/pi1_circle/Submission.lean`](examples/submissions/pi1_circle/Submission.lean),
a real proof that `π₁(S¹) ≅ ℤ`. Maintainers can run the same hosted path through
the `Evaluate submission` workflow's manual dispatch; reference smoke runs are
marked ineligible for leaderboard points.

The second maintained source-auditable proof lives at
[`examples/submissions/sphere_lower_homotopy_subsingleton/`](examples/submissions/sphere_lower_homotopy_subsingleton/).
It proves `π_k(S^n) = 0` for `k < n` in the benchmark's exact metric-sphere
model and passes Comparator, Lean with `--trust=0`, and nanoda.

## Comparator prerequisites

Local `lake test` requires `systemd-run`, `landrun`, `lean4export`, comparator, and
`nanoda_bin` on `PATH` (or `COMPARATOR_BIN` for comparator). See the
[`local setup guide`](docs/comparator-setup.md); the immutable source pins and
trust model are in [`SECURITY.md`](SECURITY.md). After installing
them, check the complete pipeline against the maintained homotopy smoke problem:

```bash
lake exe homotopy-groups-lean check-comparator-installation
lake exe homotopy-groups-lean check-eval-workflow
```

## Repository layout

- `HomotopyGroups/`: trusted definitions and benchmark statements
- `manifests/problems/`: one auditable TOML record per benchmark problem
- `generated/`: deterministic comparator workspaces
- `EvalTools/`: generator, inventory, validator, and local scorer
- `templates/`: nanoda-forcing comparator harness
- `tests/` and `scripts/`: tooling regressions and security probes
- `research/`: source-backed catalog research and scope notes
- `results/`: append-only hosted evaluator verdicts plus a derived index
- `website/`: public tracker and leaderboard

The generator layer was adapted from `leanprover/lean-eval`; see
[`NOTICE`](NOTICE) and [`LICENSE`](LICENSE).
