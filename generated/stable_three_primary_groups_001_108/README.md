# `stable_three_primary_groups_001_108`

Exact 3-primary stable groups in stems 1 through 108

- Problem ID: `stable_three_primary_groups_001_108`
- Test Problem: no
- Submitter: homotopy-groups-lean comprehensive 2026 registry
- Notes: knowledge_status=known_result/exact; one finite-indexed theorem family states the exact 3-primary subgroup in every positive stable stem from 1 through 108; generated from the audited handoff CSV; stem 0 is excluded because Z_(3) is localization rather than primary torsion.
- Source: Ravenel, Complex Cobordism and Stable Homotopy Groups of Spheres, digital third edition (2026), Table A3.2 plus the image-of-J formula: https://www.sas.rochester.edu/mth/sites/doug-ravenel/mybooks/ravenel3rd.pdf

Do not modify `Challenge.lean` or `Solution.lean`. Those files are part of the
trusted benchmark and fixed by the repository.

Write your solution in `Submission.lean` and any additional local modules under
`Submission/`.

Participants may use Mathlib freely. Any helper code not already available in
Mathlib must be inlined into the submission workspace.

Multi-file submissions are allowed through `Submission.lean` and additional local
modules under `Submission/`.

`lake test` runs comparator for this problem. The command expects a comparator
binary in `PATH`, or in the `COMPARATOR_BIN` environment variable.
