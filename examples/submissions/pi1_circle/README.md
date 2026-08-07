# Maintained circle solution

This proof solves `pi1_circle_mulEquiv_int` using the exponential covering of
the circle and the native equivalence between `π₁` and `FundamentalGroup`.

It is the repository's positive end-to-end fixture. The hosted evaluator copies
only [`Submission.lean`](Submission.lean) from this directory; it does not trust
or consume a submitted lakefile, challenge, solution bridge, toolchain, or
comparator configuration. The reference fixture is never leaderboard-eligible.
