# Literature review and lattice audit

This document audits the earlier low-stem PDF. The later comprehensive 2026
handoff and its beyond-stem-90 claim types are audited separately in
[`comprehensive-handoff-audit.md`](comprehensive-handoff-audit.md). That newer
material does not change the integral lattice rules below.

The archived report, [*Homotopy Groups of Spheres: a literature
review*](../website/public/reports/homotopy-groups-of-spheres-literature-review.pdf),
is the source for the website's 92 by 91 evidence core. The live lattice adds
eighteen columns through stem 108 so the all-degree Lean circle calculation and
the repository's 3-primary frontier share a visible range; outside the circle
row, those added columns remain uncharted. Its SHA-256 digest is
`749a0686118c9e4454b6166da0966b8097ba7ebaf2177db198bacd1f7953f9e6`.
The supplied artifact is a 33-page PDF; the CSV and BibTeX companions named in
Appendix F were not present in the attachment.

## Exact lattice interpretation

A coordinate `(n,k)` denotes `pi_(n+k)(S^n)`, for `1 <= n <= 92` and
`0 <= k <= 108`.  The complete integral source registry still ends at stem 90.
The machine-readable rule is in
[`lattice-coverage.json`](lattice-coverage.json).  In order of precedence:

1. The `n = 1` row is known integrally: `Z` at `k = 0` and zero thereafter.
2. For `n >= 2`, stems `k <= 20` are known integrally from Toda and
   Mimura--Toda.
3. The stable range is exactly `k <= n - 2`.  It inherits the stable-stem
   registry: stems 84, 85, 86, and 90 have published full-group alternatives;
   all other stems through 90 are exact.
4. In the unstable range, stems 21 through 32 are tabulated at the prime 2.
5. In stem 33, the 2-primary component is tabulated for `2 <= n <= 9` and
   `28 <= n <= 34`.
6. The coordinate `(27,33)` stays disputed.  Yang--Wu's prose and table say the
   range through 27 remains in progress, while a caption and corollary include
   27.  See [arXiv:2406.08621](https://arxiv.org/abs/2406.08621).
7. For `91 <= k <= 108`, only the `n = 1` row is assigned a complete integral
   value; every other newly displayed cell is conservatively uncharted.
8. Every remaining gray cell means *not fully tabulated by this review*, not
   “nothing is known.”

This yields 4,486 exact-integral cells, 19 cells with published integral
alternatives, 333 exact-at-2 cells, one disputed cell, and 5,189 cells not fully
tabulated.  Lean proof status is an independent overlay.  In particular, a
formal proof for one stable representative does not prove every stable cell
until suspension maps and Freudenthal equivalences have themselves been
formalized.

## Bibliographic corrections

The PDF is retained verbatim for provenance.  Consumers should apply these
metadata corrections:

- Page 21: the 31-stem source is Tomohisa Inoue, Toshiyuki Miyauchi, and Juno
  Mukai, “The 2-components of the 31-stem homotopy groups of the 9 and
  10-spheres,” *J. Fac. Sci. Shinshu Univ.* 46 (2015), 1--19.
  [Institutional record](https://soar-ir.repo.nii.ac.jp/records/11998).
- Page 23: A. K. Bousfield, “On the homotopy theory of K-local spectra at an
  odd prime,” *Amer. J. Math.* 107(4) (1985), 895--932.
  [DOI 10.2307/2374361](https://doi.org/10.2307/2374361).
- Page 24 conflates two Mikhailov--Wu papers.  “Homotopy groups as centres of
  finitely presented groups” concerns suspensions of `K(A,1)`
  ([arXiv:1108.6167](https://arxiv.org/abs/1108.6167)).  The sphere result is
  “A combinatorial description of homotopy groups of spheres”
  ([arXiv:1108.3055](https://arxiv.org/abs/1108.3055)), published as
  “Combinatorial group theory and the homotopy groups of finite complexes,”
  *Geom. Topol.* 17 (2013), 235--272
  ([DOI 10.2140/gt.2013.17.235](https://doi.org/10.2140/gt.2013.17.235)).
- Page 24: Roman Mikhailov, Jie Wu, and Sergei O. Ivanov, “On nontriviality of
  certain homotopy groups of spheres,” *Homology Homotopy Appl.* 18(2) (2016),
  337--344. [Published source](https://intlpress.com/site/pub/files/_fulltext/journals/hha/2016/0018/0002/HHA-2016-0018-0002-a018.pdf).
- Li--Li's `e`-family result currently has no journal reference in its live
  metadata, so it is cataloged as a preprint:
  [arXiv:2602.20184](https://arxiv.org/abs/2602.20184).
- Bobkova--Quigley's current version really does state five 192-periodic
  families; no correction is needed there:
  [arXiv:2410.21181v3](https://arxiv.org/abs/2410.21181v3).

The stable-stem table itself passed the audit.  It is exact through stem 83 and
again at 87--89, with alternatives only in 84, 85, 86, and 90.  The 2025
Burklund--Isaksen--Xu corrections in stems 70, 71, 82, and 83 are already
incorporated.

## Formal-statement gaps exposed by the review

The benchmark now carries direct statement families for the first and second
offsets, the low third-offset exceptions, higher circle vanishing, and positive
stable-stem finiteness.  `HomotopyGroups.TodaTable` is generated from the
versioned companion CSV and states all 400 integral entries for sphere
dimensions 1 through 20 and stems 0 through 19 in a single finite-indexed
theorem family.  The Mimura--Toda 20-stem still needs a structured
transcription. Finite primary components can use Mathlib's genuine
`CommGroup.primaryComponent`; the exact 3-primary table through stem 108 is
stated in `HomotopyGroups.StableThreePrimary`. The unstable 2-primary tables
still need a versioned transcription, while degree-zero p-local statements
still require localization.

Serre's first odd-primary torsion theorem, the Cohen--Moore--Neisendorfer
exponent theorem, suspension/Freudenthal, Hopf and Kervaire invariants,
Pontryagin--Thom, image `J`, Nishida nilpotence, chromatic localization, and
Adams spectral-sequence claims are recorded as foundation-blocked targets.
