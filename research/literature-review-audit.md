# Literature review and lattice audit

This document audits the earlier low-stem PDF and the complete-additive-group
rules projected into the lattice. The later comprehensive 2026 handoff and its
beyond-stem-90 claim types are audited separately in
[`comprehensive-handoff-audit.md`](comprehensive-handoff-audit.md). Most of that
newer material belongs in the layered stable-frontier atlas rather than the
complete-integral lattice; its copy of Thomeier's backward theorem prompted the
separate source audit recorded below.

The archived report, [*Homotopy Groups of Spheres: a literature
review*](../website/public/reports/homotopy-groups-of-spheres-literature-review.pdf),
is the archived baseline for the website's low-stem evidence core. The live
lattice also incorporates the source-audited Thomeier registry and adds eighteen
columns through stem 108 so the all-degree Lean circle calculation and the
repository's 3-primary frontier share a visible range. Its SHA-256 digest is
`749a0686118c9e4454b6166da0966b8097ba7ebaf2177db198bacd1f7953f9e6`.
The supplied artifact is a 33-page PDF; the CSV and BibTeX companions named in
Appendix F were not present in the attachment.

## Exact lattice interpretation

A coordinate `(n,k)` denotes `pi_(n+k)(S^n)`, for `1 <= n <= 92` and
`0 <= k <= 108`. The absolute-degree view instead shows `(n,m)` for
`1 <= n,m <= 92`; its lower triangle `m<n` consists of exact zero groups. The
machine-readable domain is in
[`lattice-coverage.json`](lattice-coverage.json), and the exact
backward-from-stability rules are in
[`thomeier-unstable.json`](thomeier-unstable.json). In precedence order:

1. The `n = 1` row is known integrally: `Z` at `k = 0` and zero thereafter.
2. For `n >= 2`, stems `k <= 20` are known integrally from Toda and
   Mimura--Toda.
3. The stable range is exactly `k <= n - 2`.  It inherits the stable-stem
   registry: stems 84, 85, 86, and 90 have published full-group alternatives;
   all other stems through 90 are exact.
4. Thomeier's unconditional integral structure formulas, including clauses
   with decidable arithmetic hypotheses, derive exact unstable groups from an
   exact stable row.
5. Remaining unstable cells in stems 21 through 32 are tabulated at the prime
   2, but are not thereby classified integrally.
6. In stem 33, the 2-primary component is tabulated for `2 <= n <= 9`.
   Thomeier upgrades `28 <= n <= 34` to complete integral groups.
7. The coordinate `(27,33)` is a **source conflict**. Yang--Wu's prose and
   table say the range through 27 remains in progress, while a caption and
   corollary include 27. This is a source-internal scope conflict, not two
   incompatible published group values; the complete value is not safely
   certified. See [arXiv:2406.08621](https://arxiv.org/abs/2406.08621).
8. For `91 <= k <= 108`, only the `n = 1` row is assigned a complete integral
   value; every other newly displayed cell is conservatively uncharted.
9. Every remaining gray cell means **full integral group not classified in
   current registry**. It does not mean that mathematics knows nothing about
   the group.

Lean proof status is an independent border overlay. In particular, a
formal proof for one stable representative does not prove every stable cell
until suspension maps and Freudenthal equivalences have themselves been
formalized.

## Thomeier backward-from-stability correction

Thomeier writes the `d`th group backward from stability as
`G_r^{-d} = pi_(2r-d+2)(S^(r-d+2))`. The audited generator evaluates Satz
1.1--1.8 on the exact stable rows `r=21,...,83,87,88,89`. It excludes the
already-covered baseline `r<=20` and the non-exact stable rows 84, 85, 86, and
90. Direct sums are formed with the complete integral stable group, so these
are integral statements rather than merely 2-local ones.

The result is **307 additional exact integral cells** in the 92 by 109 stem
display. Of these, 57 replace exact-2-primary-only cells and 250 replace gray
cells. Exactly **118** lie in the 92 by 92 absolute-degree display: the same 57
formerly 2-primary-only cells and 61 formerly gray cells. In particular, the
seven cells in the 33-stem at `n=28,...,34` are complete integral groups, and
`pi_49(S^25) = pi_24^S direct-sum C2` is also exact.

The critique's totals 314 and 121 included seven unsupported cells, three of
which would lie in the 92 by 92 window. They amount to assigning a nonexistent
`d=7` full-group formula in the `r = 8a+7` case, for
`r=23,39,47,55,71,79,87`. The three visible phantom coordinates would be
`(n,m)=(18,41),(34,73),(42,89)`. Satz 1.8 treats only `d=1,...,6`: its
unconditional structure formulas stop at `d=3`, while its later clauses give
equalities and orders, or structures subject to a Whitehead-product premise.
The order table leaves the `q=-7` entry blank. A later nonvanishing result does
not identify the complete additive group at `d=7`.

More generally, the registry excludes every formula whose decomposition
depends on whether a named Whitehead product is divisible by two. It also
excludes order-only statements and equalities between two otherwise unknown
groups. It does include the purely arithmetic hypotheses in Satz 1.1 and 1.3,
because “the quotient is not a power of two” and “the quotient is at least two”
are decidable for each displayed stem. This conservative distinction is why the
source-audited count is 307 rather than 314.

## Corrected display-domain counts

The statuses below are mutually exclusive display classes. “Exact integral”
means that the abstract additive group is classified; it does not assert known
generators, products, Toda brackets, filtrations, or representatives.

| View | Exact integral | Published integral alternatives | Exact 2-primary only | Source conflict | Full integral group not classified in current registry | Total |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| Absolute degree, `1 <= n,m <= 92` | 6,722 | 0 | 276 | 1 | 1,465 | 8,464 |
| Stem, `1 <= n <= 92`, `0 <= k <= 108` | 4,793 | 19 | 276 | 1 | 4,939 | 10,028 |

These are statistics of two finite display domains, not measures of the global
state of the subject. A gray cell can still contain known prime-local
components, named elements, summands, orders, products, spectral-sequence
information, or periodic families.

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
theorem family. `HomotopyGroups.MimuraTodaTable` is generated from the
source-audited 20-stem CSV and states all 21 Mimura--Toda entries for sphere
dimensions 2 through 22 in a second finite-indexed theorem family. Finite
primary components can use Mathlib's genuine
`CommGroup.primaryComponent`; the exact 3-primary table through stem 108 is
stated in `HomotopyGroups.StableThreePrimary`. The unstable 2-primary tables
still need a versioned transcription, while degree-zero p-local statements
still require localization.

Serre's first odd-primary torsion theorem, the Cohen--Moore--Neisendorfer
exponent theorem, suspension/Freudenthal, Hopf and Kervaire invariants,
Pontryagin--Thom, image `J`, Nishida nilpotence, chromatic localization, and
Adams spectral-sequence claims are recorded as foundation-blocked targets.
