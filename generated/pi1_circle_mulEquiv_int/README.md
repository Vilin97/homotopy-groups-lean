# `pi1_circle_mulEquiv_int`

The fundamental group of the circle is the integers

- Problem ID: `pi1_circle_mulEquiv_int`
- Test Problem: no
- Submitter: OpenAI Codex
- Notes: knowledge_status=derivable_from_pinned_mathlib; a comparator-safe proof uses Circle.exp, its additive quotient covering, and pi1MulEquivFundamentalGroup.
- Source: https://pi.math.cornell.edu/~hatcher/AT/AT.pdf

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
