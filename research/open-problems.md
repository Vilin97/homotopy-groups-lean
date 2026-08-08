# Open-problem registry

[`open-problems.json`](open-problems.json) separates genuine conjectures from
open computations, provisional results, and questions that are no longer open.
This distinction is part of the benchmark's trust model: a missing Lean proof of
a published theorem is not a mathematical conjecture.

Two conjectures currently have concrete, comparator-ready Lean statements:

- Isaksen--Wang--Xu's quadratic growth conjecture for cumulative two-primary
  stable stems;
- Ivanov--Mikhailov--Wu's nonvanishing conjecture for the two-primary
  component of every `π_m(S³)` above degree 10.

The comprehensive 2026 audit expands the curated registry to sixteen credible
open families. Alongside Freyd, Curtis, Moore, and unique smooth spheres, it
adds Eccles and Lannes--Zarati spherical-class predictions, Ravenel's EHP and
beta_1 patterns, both Kervaire and chromatic Mahowald-invariant predictions,
weak chromatic splitting, and very exotic spheres. Each blocked entry carries
an explicit list of missing foundations. They are not encoded using abstract
placeholder structures, since that would produce goals that look formal while
no longer stating the cited topology.

The global New Doomsday Conjecture is also retained after the report audit. In
Minami's uniform formulation, for every Adams filtration `s` there is an
`n(s)` such that no nonzero class in the image of `(Sq^0)^(n(s))` on the
mod-two Adams `E_2` page is a permanent cycle. Li--Li prove the `e`-family
case, not the global conjecture. A faithful Lean statement is blocked on
spectra and Adams spectral-sequence foundations.

The four unresolved additive extensions in stable stems 84, 85, 86, and 90 are
tracked separately in [`stable-stems.json`](stable-stems.json) as
`published_alternatives`; they are open computations, not conjectures.

Two stale labels are guarded explicitly:

- the dimension-126 Kervaire result is retained as a
  `provisional_preprint_result` from arXiv:2412.10879, not called open;
- Ravenel's telescope conjecture is marked `provisional_preprint_disproof`,
  matching the current status of the claimed counterexamples at arXiv:2310.17459.

The registry also records disposition rather than silently promoting every
handoff row to a conjecture. All 27 raw status-ledger rows are assigned to an
open conjecture, a no-longer-open or provisional result, a needed
reformulation, a research program or conditional scenario, a heuristic, or an
explicit out-of-scope record. The mixed Kervaire EHP source row is split into a
precise conditional differential conjecture and settled existence statuses.
The strong chromatic-splitting decomposition and
Kervaire classes beyond dimension 126 are no longer open; current Singer
counterexamples remain preprint-qualified; Ravenel's odd-primary EHP birth
pattern needs reformulation; redshift is retained as a research program until
a single precise formulation is sourced; and smooth four-dimensional Poincare
is explicitly marked out of this benchmark's current scope.
