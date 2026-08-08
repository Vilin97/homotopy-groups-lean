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

Freyd's generating hypothesis, the Curtis spherical-classes conjecture, the
Moore exponent conjecture, and the unique-smooth-spheres conjecture remain in
the machine-readable registry with exact missing-foundation lists. They are not
encoded using abstract placeholder structures, since that would produce goals
that look formal while no longer stating the cited topology.

The global New Doomsday Conjecture is also retained after the report audit.  It
asserts that every nonzero `Sq^0`-family in the mod-two Adams `E_2` page has
only finitely many survivors.  Li--Li prove the `e`-family case, not the global
conjecture.  A faithful Lean statement is blocked on spectra and Adams
spectral-sequence foundations.

The four unresolved additive extensions in stable stems 84, 85, 86, and 90 are
tracked separately in [`stable-stems.json`](stable-stems.json) as
`published_alternatives`; they are open computations, not conjectures.

Two stale labels are guarded explicitly:

- the dimension-126 Kervaire result is retained as a
  `provisional_preprint_result` from arXiv:2412.10879, not called open;
- Ravenel's telescope conjecture is marked `provisional_preprint_disproof`,
  matching the current status of the claimed counterexamples at arXiv:2310.17459.
