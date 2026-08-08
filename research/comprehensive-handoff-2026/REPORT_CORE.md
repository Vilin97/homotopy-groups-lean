# Homotopy Groups of Spheres: Formalization-Oriented Research Survey

**State-of-knowledge cutoff:** 8 August 2026  
**Package role:** Narrative companion to the canonical machine-readable ledgers in `data/`.

> Dense numerical appendices and bibliography tables were deliberately removed from this Markdown file. Their non-redundant, canonical versions are the CSV ledgers listed in `README.md`.

# Abstract

The homotopy groups π_m(S^n) are elementary to define and extraordinarily difficult to compute. This report synthesizes the classical non-equivariant subject through 8 August 2026 and distinguishes stable from unstable information, integral from prime-local results, additive groups from products and extensions, and peer-reviewed theorems from current preprints. The exact integral stable additive groups are known through stem 83; stems 84-90 have localized 2-primary ambiguities, with stems 87-89 exact. At odd primes the numerical record extends much farther: the complete 3-primary groups are tabulated through stem 108, while Ravenel’s 2026 p=5 computation reaches the 1000-stem and its table runs through stem 999, preserving four source-marked question entries. The image of J and the full height-one pattern are known in all dimensions. Beyond finite tables, current work gives 125 explicit 192-periodic 2-primary height-two families in nineteen residue classes, extensive 144-periodic 3-primary product families, the claimed Kervaire class θ_6 in stem 126, uniform Adams differentials on the h_j^3 and e-families, and all-height telescope counterexamples in preprint form. Unstably, all-prime groups are complete through the 20-stem, the 2-primary all-sphere calculation through the 32-stem, and Toda’s complete 3-primary tables through the 79-stem in his convention. The report supplies full numerical ledgers, a 27-item conjecture status table, 2024-2026 source updates, and machine-readable companion files.

## How to use this package

- Read Sections 1-15 for definitions, structural theorems, computational methods, geometry, and historical context.
- Read Supplement S1-S9 for the audited beyond-stem-90 record, conjecture status, and 2024-2026 updates.
- Treat `data/*.csv` as canonical for dense numerical tables. The Markdown survey summarizes them but does not duplicate them.
- Use the `status` fields before translating any row into a theorem: exact published results, partial alternatives, source-marked uncertainties, and preprint claims are intentionally distinguished.
- Use `data/source_ledger.csv` for the bibliography and source inventory.

# Executive summary: the state of the subject in 2026

There is no closed formula for π_m(S^n), no known algorithm competitive with specialized spectral-sequence calculations in the ranges mathematicians care about, and no finite list of families that accounts for all stable homotopy. Nevertheless, the combination of classical composition methods, chromatic structure, and modern motivic/synthetic computation gives a precise and surprisingly rich body of knowledge. The following table is the shortest accurate summary of the numerical frontier.

| **Object**                     | **Range**                           | **2026 status**                                                                   | **Principal sources**                                      |
|--------------------------------|-------------------------------------|-----------------------------------------------------------------------------------|------------------------------------------------------------|
| **Integral stable groups**     | π_k^S for 0≤k≤83                    | Complete additive groups                                                          | IWX 2023; Burklund-Isaksen-Xu 2025 corrections/completions |
| **Stable stems 84-90**         | Integral                            | Partial; explicit 2-primary alternatives                                          | IWX 2023, with later corrections incorporated              |
| **Stable p=3**                 | 0≤k≤108                             | Complete p-local additive groups through 108                                      | Tangora, Aubry, Ravenel; surveyed Wang-Xu 2023             |
| **Stable p=5**                 | 0≤k≤999                             | Computation to the 1000-stem; table through 999 with four source-marked ? entries | Ravenel 2026, Table A3.3, plus image-J formula             |
| **Integral unstable k-stems**  | π\_{n+k}(S^n), all n≥2, k≤20        | Complete                                                                          | Toda 1962; Mimura-Toda 1963                                |
| **2-primary unstable k-stems** | All n≥2, k≤32                       | Complete                                                                          | Mimura; Mimura-Mori-Oda; Oda; Inoue-Mukai; Miyauchi-Mukai  |
| **2-primary unstable 33-stem** | n=2-9 and n≥28                      | Known; n=10-27 incomplete                                                         | Oda; Miyauchi-Mukai; Yang-Wu 2026; Thomeier                |
| **Kervaire invariant one**     | Dimensions 2,6,14,30,62,126 only    | Last case claimed resolved                                                        | Lin-Wang-Xu 2025 preprint; HHR 2016                        |
| **Telescope conjecture**       | Heights ≥2, every prime             | Claimed false                                                                     | Burklund-Hahn-Levy-Schlank preprint                        |
| Unstable p=3                   | π\_{n+k}(S^n)\_(3), k\<80           | Complete prime-local all-sphere tables in Toda’s convention                       | Toda 2003                                                  |
| 2-primary height two           | 125 families in 19 residues mod 192 | Explicit nonzero periodic families, including order 4 and 8                       | Carrick-Davies 2025/2026; BBQ; Bobkova-Quigley             |
| Height-one/J families          | All dimensions                      | Closed formulas for image J and v1-periodic summands                              | Adams; Quillen; Sullivan; Mahowald; Ravenel                |

*Table 1. Numerical and structural frontier as of 8 August 2026.*

## The most important updates after the 2023 0-90 computation

<table>
<colgroup>
<col style="width: 100%" />
</colgroup>
<thead>
<tr class="header">
<th><p><strong>Stable stems 82 and 83.</strong> The 2-primary components are π_82^S(2)=(Z/2)^6 + Z/8 and π_83^S(2)=(Z/2)^3 + (Z/8)^2.</p>
<p><em>Source: Burklund-Isaksen-Xu, Peking Mathematical Journal, 2025. Status: Published.</em></p></th>
</tr>
</thead>
<tbody>
</tbody>
</table>

<table>
<colgroup>
<col style="width: 100%" />
</colgroup>
<thead>
<tr class="header">
<th><p><strong>Corrections in stems 70 and 71.</strong> The corrected 2-primary v1-torsion groups are (Z/2)^6 + Z/4 and (Z/2)^5 + Z/4 + Z/8, respectively; a previously asserted hidden 2-extension in stem 70 is absent.</p>
<p><em>Source: Burklund-Isaksen-Xu, 2025. Status: Published.</em></p></th>
</tr>
</thead>
<tbody>
</tbody>
</table>

<table>
<colgroup>
<col style="width: 100%" />
</colgroup>
<thead>
<tr class="header">
<th><p><strong>Last Kervaire class.</strong> A preprint proves h_6^2 is a permanent cycle and concludes that Kervaire-invariant-one framed manifolds exist exactly in dimensions 2, 6, 14, 30, 62, and 126.</p>
<p><em>Source: Lin-Wang-Xu, arXiv:2412.10879v2. Status: Preprint.</em></p></th>
</tr>
</thead>
<tbody>
</tbody>
</table>

<table>
<colgroup>
<col style="width: 100%" />
</colgroup>
<thead>
<tr class="header">
<th><p><strong>Telescope conjecture.</strong> A preprint constructs counterexamples at every prime and every chromatic height at least 2; height 0 and height 1 remain the positive cases.</p>
<p><em>Source: Burklund-Hahn-Levy-Schlank, arXiv:2310.17459. Status: Preprint.</em></p></th>
</tr>
</thead>
<tbody>
</tbody>
</table>

<table>
<colgroup>
<col style="width: 100%" />
</colgroup>
<thead>
<tr class="header">
<th><p><strong>New height-two families.</strong> Recent work supplies many 192-periodic 2-primary families, including classes invisible to tmf but detected T(2)- and K(2)-locally, plus new simple 4- and 8-torsion families and geometric consequences for exotic spheres.</p>
<p><em>Source: Bhattacharya-Bobkova-Quigley; Bobkova-Quigley; Carrick-Davies. Status: Mixed: published and preprint.</em></p></th>
</tr>
</thead>
<tbody>
</tbody>
</table>

## What remains unknown

Even the additive stable groups are not completely settled in stems 84-90, and essentially no contiguous integral range beyond 90 is known. Ext groups and partial Adams information extend much farther than the actual homotopy groups, but unresolved differentials and hidden extensions prevent a complete answer.

On the unstable side, the complete all-sphere 2-primary record stops at the 32-stem. The next stem remains incomplete for sphere dimensions 10 through 27. There is no analogous clean, modern, all-prime unstable table far beyond Toda’s 20-stem.

Chromatic theory predicts and constructs periodic structure without classifying all elements. At every height, the gap between localized information and the actual sphere is substantial. The telescope counterexamples sharpen this distinction: finite localization and Bousfield localization no longer agree from height two onward.

The multiplicative ring π\_\*^S, not merely its additive groups, is much less completely recorded. A table of groups does not determine products, Toda brackets, power operations, or the maps induced by finite complexes. Modern computations therefore maintain charts and relation databases rather than a single list of abelian groups.

# 1. Scope, conventions, and evidence standards

## 1.1 Classical scope

The primary subject is the classical based homotopy group π_m(S^n)=\[S^m,S^n\]\_\* and its stable limit. Equivariant, motivic, and synthetic homotopy groups are included only where they furnish computations or structural explanations for the classical sphere. A genuinely exhaustive review of motivic or equivariant sphere stems would be a separate report of comparable size.

The phrase “all known results” is interpreted at the level appropriate for a literature review: every major global theorem, every published complete numerical range, all standard named infinite families, the principal multiplicative and chromatic structures, the important geometric applications, and an annotated source map for specialized relations. It is neither useful nor feasible to restate every individual Toda relation or every chart differential. Those are indexed to their primary sources and datasets.

## 1.2 Notation

| **Symbol**        | **Meaning**                                                                    |
|-------------------|--------------------------------------------------------------------------------|
| **π_m(S^n)**      | Based homotopy classes S^m -\> S^n.                                            |
| **π\_{n+k}(S^n)** | The unstable k-stem at sphere dimension n.                                     |
| **π_k^S**         | Stable limit colim_n π\_{n+k}(S^n); equivalently π_k of the sphere spectrum.   |
| **G\_(p), G_p^∧** | p-localization and p-completion, respectively.                                 |
| **π_k^S(p)**      | The p-primary finite subgroup in positive stems.                               |
| **E, H, P**       | Suspension, Hopf-invariant map, and Whitehead-product map in the EHP sequence. |
| **η, ν, σ**       | The stable Hopf-invariant-one classes in stems 1, 3, and 7.                    |
| **α, β, γ**       | Greek-letter families, usually organized by chromatic height.                  |
| **v_n**           | A periodicity operator detected at chromatic height n.                         |
| **J**             | The stable J-homomorphism π\_\*(O) -\> π\_\*^S.                                |

## 1.3 Evidence labels and date sensitivity

Peer-reviewed computations are treated as established, subject to explicit later corrections. Accepted or forthcoming work is identified as such. ArXiv results without a journal reference at the cutoff are called preprints even when experts broadly regard them as convincing. This matters particularly for the last Kervaire invariant problem and the all-height counterexamples to the telescope conjecture.

Numerical tables are versioned objects. `data/stable_stems_0_90.csv` uses IWX 2023 as the base, replaces the incorrect 70- and 71-stem entries, incorporates the 2025 completion of stems 82 and 83, and retains IWX’s explicit alternatives in stems 84-90. Section 4.4 and `data/unstable_computation_coverage.csv` record the internal n=27 inconsistency in Yang-Wu rather than choosing the stronger caption over the contradictory prose and table.

<table>
<colgroup>
<col style="width: 100%" />
</colgroup>
<thead>
<tr class="header">
<th><p><strong>Warning about “computed through N”</strong></p>
<p>In this literature, “computed through stem N” may mean different things: an Ext chart exists, the E_infinity page is known, the additive p-primary groups are known, all hidden extensions are resolved, multiplicative products are known, or all primes have been assembled integrally. This report states which meaning is intended each time.</p></th>
</tr>
</thead>
<tbody>
</tbody>
</table>

# 2. Elementary and global structure of π_m(S^n)

## 2.1 Definition, functoriality, and the first groups

For pointed spaces, π_m(S^n) is the set of based homotopy classes of maps S^m -\> S^n. It is a group for m≥1 and abelian for m≥2. Cellular approximation gives π_m(S^n)=0 for m\<n. The degree theorem gives π_n(S^n)=Z, generated by the identity. The action of degree-d self-maps and composition make sphere homotopy into a network of modules and pairings rather than a collection of unrelated groups.

The first unstable deviations already display the characteristic mixture of free and torsion information. The Hopf fibration generates π_3(S^2)=Z. For n≥3, π\_{n+1}(S^n)=Z/2, generated by a suspension of η. For every n≥2, π\_{n+2}(S^n)=Z/2. In the next stem the exceptional low spheres appear: π_5(S^2)=Z/2, π_6(S^3)=Z/12, π_7(S^4)=Z+Z/12, while the stable group is π_3^S=Z/24.

## 2.2 Freudenthal stabilization

Freudenthal’s suspension theorem says that E:π\_{n+k}(S^n)-\>π\_{n+k+1}(S^{n+1}) is an isomorphism when n≥k+2 and a surjection when n=k+1. Consequently, for fixed k, the k-stem becomes independent of n, and π_k^S may be identified with π\_{n+k}(S^n) in the stable range. This is the fundamental reason a single stable table controls infinitely many unstable groups.

The boundary of the stable range is mathematically rich. Immediately below it, Whitehead products and Hopf invariants contribute free summands and extensions. Thomeier’s theorem recovers the first eight groups counted backward from stability from the stable stem, with congruence-dependent extra Z and Z/2 summands. Modern 33-stem work still uses this 1966 result.

## 2.3 Serre finiteness and rational homotopy

Serre proved that π_m(S^n) is finite except in the diagonal m=n and, when n is even, in degree m=2n-1. Rationally, an odd sphere has a single nonzero group: π_n(S^n)⊗Q=Q. An even sphere has two: Q in degree n and Q in degree 2n-1. The latter generator is represented rationally by the Whitehead square. Thus all positive stable stems are finite.

Because every positive stable stem is a finite abelian group, it decomposes canonically into p-primary components. Serre’s first-torsion theorem implies that for odd p and n≥3, no p-torsion occurs before offset 2p-3, and the first p-torsion is a Z/p class in that offset. For a fixed stable stem k, only primes p with 2p-3≤k can occur. This simple inequality is why complete integral assembly is possible after finitely many prime-local computations.

## 2.4 Nonvanishing and size

Finiteness is not vanishing. Ivanov-Mikhailov-Wu proved that π_m(S^2) is nonzero for every m≥2; the Hopf fibration then gives nonvanishing of π_m(S^3) for every m≥3. Stable groups, by contrast, do vanish in sporadic positive stems, for example stems 4, 5, 12, and 61, but there is no classification of vanishing stems.

Burklund proved that, at each prime, the torsion exponent of π_k^S grows sublinearly in k. The p-rank is bounded by exp(O((log k)^3)), hence the stable stems have subexponential size. An appendix with Senger bootstraps this to p-local unstable sphere homotopy. The best general lower bounds remain much smaller and arise from image J and periodic families; the true asymptotic growth is open.

## 2.5 Stable homotopy as framed bordism

The Pontryagin-Thom construction identifies π_k^S with the framed bordism group Ω_k^fr. A stable map is represented by the inverse image of a regular value, a k-manifold with a stable normal framing; homotopy corresponds to framed cobordism. This is not merely an interpretation: it is the bridge to exotic spheres, characteristic numbers, the Kervaire invariant, and differential topology.

Composition and smash product make π\_\*^S a graded-commutative ring. The additive group table records only the underlying abelian groups. Framed-manifold products, compositions among η, ν, σ, and higher Toda brackets encode additional data that remains incompletely catalogued even within the computed range.

# 3. Unstable computational machinery

## 3.1 The EHP sequence and James construction

The James construction models ΩΣX by a free monoid on X up to homotopy. Applied to spheres, its Hopf construction yields the EHP fiber sequence and long exact sequence. In one standard indexing, the maps relate π\_{q+1}(S^{2n+1}), π\_{q-1}(S^n), π_q(S^{n+1}), and π_q(S^{2n+1}) through P, E, and H. Suspension moves toward stability; H measures Hopf-invariant information; P is built from Whitehead products.

Toda’s tables were obtained by repeatedly threading known generators and relations through EHP. The method is inductive but not mechanical: exactness gives kernels and cokernels, while extension problems require compositions, Hopf invariants, Whitehead products, and secondary operations. The modern 33-stem extension problems are direct descendants of this methodology.

## 3.2 Whitehead products, Hilton-Milnor, and secondary composition

The Whitehead product \[α,β\] measures the failure of wedge inclusions to commute. The Whitehead square \[ι_n,ι_n\] controls the first unstable obstruction to suspension and produces the rational class in π\_{2n-1}(S^n) for even n. The Hilton-Milnor theorem decomposes loops on a wedge into products indexed by basic Lie words, reducing many wedge problems to sphere groups plus iterated Whitehead products.

When ordinary composition vanishes for nonunique reasons, Toda brackets record secondary composition. A bracket \<α,β,γ\> is a coset modulo an explicit indeterminacy, and higher or matric brackets organize longer chains. Toda brackets both construct elements and detect hidden extensions in spectral sequences. A large fraction of named stable classes - including Kervaire and Greek-letter phenomena in low filtration - are most naturally specified by such brackets.

## 3.3 Spectral sequences in the unstable setting

The Serre spectral sequence for path-loop fibrations and iterated loop spaces supplied Serre’s early computations. The unstable Adams spectral sequence computes p-completed homotopy from unstable modules over the Steenrod algebra. The lambda algebra packages the mod-2 unstable Adams E_1 or E_2 structure and historically enabled extensive calculations. Bousfield-Kan completion, unstable modules, and Lannes theory provide additional organization.

Unlike the stable Adams spectral sequence, unstable differentials depend on the target sphere dimension and interact with EHP. Consequently, a stable chart cannot simply be desuspended. The failure of desuspension is measured by Hopf invariants, Whitehead products, and geometric boundary theorems.

## 3.4 Exponents and power maps

For an odd prime p, Cohen-Moore-Neisendorfer proved that p^n annihilates the p-primary torsion in all homotopy groups of S^{2n+1}; equivalently, a suitable p^n power map on an iterated loop space is null. This is one of the strongest uniform unstable results. Subsequent work of Gray, Anick, Neisendorfer, and others refines decompositions and exponents in special dimensions and primes.

At p=2, exponent behavior is subtler and lacks a comparably uniform theorem. The Moore conjecture and related exponent questions for finite complexes remain part of the broader attempt to distinguish elliptic and hyperbolic homotopy growth.

## 3.5 Chromatic unstable homotopy and Goodwillie calculus

The Bousfield-Kuhn functor extracts v_n-periodic unstable homotopy and returns a T(n)-local spectrum. Goodwillie’s Taylor tower of the identity functor approximates a space by homogeneous layers built from derivatives carrying symmetric-group actions. Arone-Mahowald showed that, for spheres, only selected layers contribute to v_n-periodic homotopy, turning an unstable problem into a structured stable calculation.

Modern work recasts the layers using spectral Lie algebras, partition complexes, and unstable chromatic categories. These methods do not yet supply an integral table, but they explain why periodic unstable families exist and how their sphere dimension controls desuspension.

# 4. The unstable numerical record

## 4.1 Complete ranges

| **k-stem** | **Localization/range**    | **Primary source**                     | **Status**                                            |
|------------|---------------------------|----------------------------------------|-------------------------------------------------------|
| **0-19**   | Integral, all n≥1         | Toda 1962                              | Complete table of π\_{n+k}(S^n).                      |
| **20**     | Integral, all n           | Mimura-Toda 1963                       | Completes the all-prime 20-stem.                      |
| **21-22**  | 2-primary, all n          | Mimura 1965                            | Generalized Hopf homomorphism and higher composition. |
| **23-24**  | 2-primary, all n          | Mimura-Mori-Oda 1975                   | Complete 2-components.                                |
| **25-31**  | 2-primary, all n≥2        | Oda 1979; later corrections            | Remaining 31-stem issues resolved by Inoue-Mukai.     |
| **32**     | 2-primary, all n≥2        | Miyauchi-Mukai 2017                    | Complete.                                             |
| **33**     | 2-primary, n=2-9 and n≥28 | Oda; Miyauchi-Mukai; Yang-Wu; Thomeier | n=10-27 incomplete; n=27 source inconsistency.        |

*Table 2. Complete and near-complete unstable ranges.*

This ledger is more informative than saying that “homotopy groups of spheres are known to the 32-stem.” The integral record stops at 20; the extension to 32 is a 2-primary result. Odd-primary unstable calculations continue much farther in many selected dimensions and families, but they do not form a comparably clean all-sphere range.

The generator-level 2-primary tables in the Wang-Xu survey and Oda’s monograph-length paper remain indispensable. They record not only abelian groups but named generators, suspensions, Hopf invariants, P-images, and compositions needed to continue EHP calculations.

## 4.2 Toda’s table through the 19-stem

`data/toda_unstable_stems_0_19.csv` reproduces the complete integral table from Toda’s *Composition Methods*, organized by offset k and sphere dimension n. It is the largest compact all-prime unstable table that remains standard. The entries exhibit stabilization diagonally, free Z summands in the Whitehead-square degree for even spheres, and the rapid proliferation of 2-primary summands.

A table entry such as 8+2+3 means Z/8 + Z/2 + Z/3, “infty” means Z, and 1 means the trivial group. The CSV companion preserves this compact notation so it can be compared against online databases or transformed programmatically.

## 4.3 Selected exact low-stem formulas

| **Case**                | **Group/theorem**                                               | **Range**                 |
|-------------------------|-----------------------------------------------------------------|---------------------------|
| **k=0**                 | π_n(S^n)=Z                                                      | All n≥1                   |
| **k=1**                 | π_2(S^1)=0; π_3(S^2)=Z; π\_{n+1}(S^n)=Z/2                       | n≥3 for stable formula    |
| **k=2**                 | π\_{n+2}(S^n)=Z/2                                               | All n≥2                   |
| **k=3**                 | π_5(S^2)=Z/2; π_6(S^3)=Z/12; π_7(S^4)=Z+Z/12; stable group Z/24 | Exceptional desuspensions |
| **rational**            | π_m(S^n)⊗Q=Q for m=n, and also m=2n-1 when n even; otherwise 0  | Serre                     |
| **first odd-p torsion** | No p-torsion for k\<2p-3; a Z/p occurs at k=2p-3                | n≥3, p odd                |

## 4.4 The 2-primary 33-stem

Yang-Wu resolve the three Oda extension problems by constructing an element κ′\_6 of order four and tracking its suspensions. Their final groups are π_39(S^6)\_(2)=Z/4+(Z/2)^6, π_40(S^7)\_(2)=Z/4+(Z/2)^4, and π_41(S^8)\_(2)=Z/8+Z/4+(Z/2)^6.

Their Table 1 combines these with earlier calculations and Thomeier’s backward theorem. However, the surrounding prose says the cases 10≤n≤27 are still being worked on, while the caption and corollary state n≥27; the table itself begins at n=28. Until an erratum or later paper resolves this, the conservative complete range is n≥28, with n=27 unresolved.

| **n**  | **π\_{n+33}(S^n) at 2**         | **Basis/status**                                            |
|--------|---------------------------------|-------------------------------------------------------------|
| **2**  | Z/4 + (Z/2)^2                   | Oda; summarized by Yang-Wu                                  |
| **3**  | (Z/2)^3                         | Oda; summarized by Yang-Wu                                  |
| **4**  | (Z/8)^2 + (Z/2)^6               | Oda; summarized by Yang-Wu                                  |
| **5**  | (Z/2)^4                         | Oda; summarized by Yang-Wu                                  |
| **6**  | Z/4 + (Z/2)^6                   | Yang-Wu 2026                                                |
| **7**  | Z/4 + (Z/2)^4                   | Yang-Wu 2026                                                |
| **8**  | Z/8 + Z/4 + (Z/2)^6             | Yang-Wu 2026                                                |
| **9**  | (Z/2)^6                         | Miyauchi-Mukai 2017                                         |
| **27** | unresolved / source discrepancy | Yang-Wu text says project covers 10-27; caption says n\>=27 |
| **28** | (Z/2)^5                         | Thomeier backward theorem + stable 33-stem                  |
| **29** | (Z/2)^5                         | same                                                        |
| **30** | (Z/2)^5                         | same                                                        |
| **31** | (Z/2)^6                         | same                                                        |
| **32** | (Z/2)^7                         | same                                                        |
| **33** | (Z/2)^6                         | same                                                        |
| **34** | (Z/2)^5 + Z\_(2)                | same                                                        |
| **35** | (Z/2)^5                         | stable and all n\>=35                                       |

*Table 3. Known 2-primary groups in the unstable 33-stem; n=27 is deliberately flagged.*

## 4.5 Odd-primary unstable information

Odd-primary unstable homotopy is structurally cleaner in several respects: the first torsion is later, odd spheres admit useful p-local splittings, and power maps have strong exponent bounds. Toda, Mimura, Oka, and many later authors computed extensive α- and β-family desuspensions, EHP differentials, and homotopy groups of Lie groups. These results are distributed across specialized papers rather than a single modern complete table.

At an odd prime, the α-family begins in stable stem 2p-3 and has period 2p-2 in its height-one form. Unstable representatives exist only above dimension-dependent bounds. The β-family is height two and interacts with double suspension, Moore spaces, and finite H-spaces. Ravenel’s book and the Wang-Xu survey are the best entry points to the classical computations; modern work tends to formulate odd-primary information chromatically rather than as all-sphere tables.

## 4.6 Why the unstable frontier advances slowly

Each new unstable stem requires more than knowing the stable endpoint. One must determine how far each stable generator desuspends, compute EHP kernels and images, resolve group extensions, and prove relations among named unstable representatives. A single unresolved order-four versus two-copies-of-order-two extension changes the group even when every associated graded piece is known.

The 2026 paper on relations in the 24th homotopy groups illustrates the dependency chain: relations established in one offset may be prerequisites for a much higher stem because compositions with σ, κ-bar, and generalized P-images propagate. Thus “old” low-stem identities can remain the bottleneck for new calculations decades later.

# 5. Stable computation: from Adams to synthetic spectra

## 5.1 The stable category and the sphere spectrum

Stabilization formally inverts suspension and replaces spaces by spectra. The sphere spectrum S is the tensor unit, and π_k^S=\[Σ^k S,S\]. Negative groups vanish because the classical sphere spectrum is connective; π_0^S=Z; positive groups are finite. Stable maps admit cofiber sequences, exact triangles, Spanier-Whitehead duality, generalized homology and cohomology theories, and spectral sequences unavailable in the same form unstably.

The computational problem is nevertheless difficult because S is the initial E_infinity ring spectrum and therefore contains every chromatic layer. A generalized cohomology theory sees only part of S. Stable homotopy calculations proceed by covering or resolving S with spectra whose cooperations are algebraically tractable, then reconstructing the missing extensions and multiplicative structure.

## 5.2 The Adams spectral sequence

At a prime p, the mod-p Adams spectral sequence has E_2^{s,t}=Ext_A^{s,t}(F_p,F_p) and converges to the p-completed stable stem π\_{t-s}^S. The filtration s measures the complexity of a class with respect to ordinary mod-p cohomology. The Steenrod algebra A is explicitly known but enormous; computing Ext requires resolutions, the lambda algebra, the May spectral sequence, secondary operations, and substantial computer algebra.

An E_infinity chart is only an associated graded object. To recover π\_\*^S one must determine hidden p-extensions and hidden multiplications by η, ν, and other classes. Differentials can be forced by naturality through finite complexes, Kahn-Priddy transfer, geometric boundary theorems, comparison with generalized cohomology theories, or Toda-bracket convergence. The 61-stem and 82-83 stem proofs are paradigmatic examples.

## 5.3 May and secondary Steenrod machinery

The May spectral sequence filters the Steenrod algebra and computes its Ext from a more accessible graded object. It identifies families such as h_i, b\_{i,j}, and their products, but then introduces its own differentials and hidden multiplicative extensions. Bruner’s computer resolution and the Bruner-Rognes Ext database make the low-dimensional E_2 page reproducible.

Secondary Steenrod algebras and Baues-Jibladze or Nassau models seek to compute Adams d_2 and higher structure algebraically. Chua’s modern work on Adams differentials via secondary operations and the Lin-Wang-Xu machine framework continue this program. These approaches are especially valuable because spectral-sequence charts contain many differential possibilities that cannot be excluded by degree alone.

## 5.4 The Adams-Novikov spectral sequence and chromatic filtration

Complex cobordism MU and its p-typical summand BP replace the Steenrod algebra by the Hopf algebroid of formal group laws. The Adams-Novikov spectral sequence has E_2=Ext\_{BP\_\*BP}(BP\_\*,BP\_\*) and converges to the p-local stable stems. Its filtration is often closer to chromatic complexity: image-J classes lie at height one, β-families at height two, and higher Greek-letter families at increasing heights.

The chromatic spectral sequence resolves the moduli stack of formal groups by height strata. Miller-Ravenel-Wilson used it to construct periodic families and Ravenel systematized the subject. At small primes the algebra remains formidable, but the Adams-Novikov viewpoint explains periodicity and supports the long classical p=3 and p=5 computations.

## 5.5 bo-, tmf-, and finite-resolution methods

At height one, real K-theory and the connective image-of-J spectrum j organize v1-periodic information and isolate v1-torsion. Mahowald’s bo-resolutions and Davis-Mahowald techniques produced many 2-primary calculations and vanishing curves. At height two, topological modular forms tmf and resolutions by spectra with level structure detect modular and periodic families.

A generalized cohomology theory can both detect and fail to detect. A class with nonzero tmf-Hurewicz image is certified, but a class invisible to tmf may still survive in the sphere. Recent 192-periodic families are specifically important because they demonstrate systematic height-two homotopy beyond ordinary tmf detection.

## 5.6 Motivic deformation and the cofiber of tau

Over C, motivic stable homotopy introduces a weight grading and an element tau. Inverting tau recovers classical stable homotopy, while the cofiber Ctau has an algebraic homotopy category closely related to BP\_\*BP comodules. This turns classical Adams-Novikov information into a geometric deformation parameter and exposes hidden extensions that are difficult to see classically.

Isaksen used the motivic May and Adams spectral sequences to compute through stem 59. Wang-Xu and Isaksen-Wang-Xu combined motivic charts, cofiber-of-tau comparisons, finite-complex arguments, and machine Ext calculations to reach 90. The method is not merely “compute motivically and invert tau”: one must prove motivic differentials, compare filtrations, and solve tau-, 2-, η-, and ν-extensions.

## 5.7 Synthetic spectra and the 2025 corrections

Synthetic spectra provide another deformation of stable homotopy, with a parameter lambda that records Adams filtration history. A classical d_r differential corresponds to lambda^{r-1}-torsion in the synthetic category. This extra structure can prove differentials and extensions by constructing finite synthetic complexes and maps whose classical shadows force the desired behavior.

Burklund-Isaksen-Xu use F_2-synthetic methods to prove that h_6 g+h_2 e_2 is a permanent cycle, completing the 82- and 83-stems. They also incorporate machine-discovered corrections to a d_5 differential, changing the 70- and 71-stem groups. This episode demonstrates why even peer-reviewed tables require versioned correction ledgers.

## 5.8 Historical computation frontier

| **Period**    | **Principal authors**                      | **Milestone**                                                              |
|---------------|--------------------------------------------|----------------------------------------------------------------------------|
| **1951-1953** | Serre                                      | Stable stems below 9 using loop-space homology and spectral sequences.     |
| **1962**      | Toda                                       | Integral stable and unstable information through the 19-stem.              |
| **1964-1965** | May and early Adams school                 | Ext computations and stable range through roughly 28.                      |
| **1967-1984** | Mahowald, Tangora, Barratt, Bruner, others | 2-primary classical computations into the 40s; extensive odd-primary work. |
| **1990-1995** | Kochman; Kochman-Mahowald                  | Computer-assisted consolidation through approximately stem 47.             |
| **2015-2019** | Isaksen and collaborators                  | Motivic 2-primary computation through 59; corrections in 51-52.            |
| **2017**      | Wang-Xu                                    | 61-stem vanishing.                                                         |
| **2020-2023** | Isaksen-Wang-Xu                            | Mostly complete 2-primary computation through 90.                          |
| **2025**      | Burklund-Isaksen-Xu                        | Complete 82-83; correct 70-71.                                             |

*Table 4. A compressed history of the stable numerical frontier.*

# 6. The stable numerical record

## 6.1 Exact integral groups through stem 83

`data/stable_stems_0_90.csv` gives the additive decomposition of every integral stable stem through 90. Through stem 83, the groups are exact after incorporating the 2025 corrections. “Exact” here means the finite abelian group is determined. It does not mean that every generator has a canonical name or that every product and Toda bracket is known.

IWX organize each group into 2-primary v1-torsion, odd-primary v1-torsion, and a v1-periodic subgroup. This decomposition is computationally and chromatically informative, though not always a canonical decomposition of rings. The table in this report preserves the columns and also prints the total additive group.

## 6.2 Stems 84-90

| **Stem** | **2-primary v1-torsion**                                                     | **Odd v1-torsion** | **v1-periodic**         | **Status**                                |
|----------|------------------------------------------------------------------------------|--------------------|-------------------------|-------------------------------------------|
| **84**   | (Z/2)^6 OR (Z/2)^5                                                           | (Z/3)^2            | 0                       | partial: one unresolved Z/2               |
| **85**   | (Z/2)^6 + (Z/4)^2 OR (Z/2)^5 + (Z/4)^2 OR (Z/2)^4 + (Z/4)^3 OR (Z/2)^7 + Z/4 | (Z/3)^2            | 0                       | partial: extension/differential ambiguity |
| **86**   | (Z/2)^4 + (Z/8)^2 OR (Z/2)^2 + Z/4 + (Z/8)^2                                 | Z/3 + Z/5          | 0                       | partial: 2-primary ambiguity              |
| **87**   | (Z/2)^5 + Z/4                                                                | 0                  | Z/16 + Z/3 + Z/5 + Z/23 | exact                                     |
| **88**   | (Z/2)^4 + Z/4                                                                | 0                  | Z/2                     | exact                                     |
| **89**   | (Z/2)^3                                                                      | 0                  | (Z/2)^2                 | exact                                     |
| **90**   | (Z/2)^3 + Z/8 OR (Z/2)^2 + Z/8                                               | Z/3                | Z/2                     | partial: one unresolved Z/2               |

*Table 5. Explicit unresolved alternatives in the top of the 0-90 range.*

The ambiguity in stem 84 is one possible Z/2. Stem 85 has several possible extension patterns, and stem 86 differs by a Z/2 versus Z/4 contribution. Stem 90 again has one possible Z/2. By contrast, the additive groups in stems 87, 88, and 89 are exact. Thus the uncertainty inside the 84-90 window is localized rather than present in every row.

There is information beyond stem 90 - Ext classes, individual differentials, periodic elements, Kervaire-related classes in 126, and localized families - but not a complete contiguous table of integral stable groups. The existence of a class in stem 126 does not imply knowledge of π_126^S as an abelian group.

## 6.3 Odd-prime numerical ranges

The classical literature, consolidated in Ravenel’s July 2026 digital third edition, records complete p=3 stable groups through stem 108. At p=5, Ravenel computes to the 1000-stem and Table A3.3 records non-J classes and relations through stem 999; four entries in the current table carry explicit question marks and are preserved as such in this report. These long odd-primary ranges should not be confused with integral ranges: the 2-primary component remains the bottleneck.

For primes p≥7, general vanishing lines and sparse Greek-letter calculations cover large regions, and any fixed low stem contains no p-torsion once 2p-3 exceeds the stem. There is not a single standard “complete through N” claim for every larger prime analogous to p=3 and p=5. The practical source is Ravenel’s green book together with later correction and family papers.

## 6.4 Multiplicative information is a separate frontier

The ring π\_\*^S is graded-commutative, and composition products can be nonzero even when additive generators are ambiguous. Named relations such as ην=0 or νσ-type products, orders of κ and κ-bar families, and products among periodic classes are distributed across Toda, Adams, Mahowald, Ravenel, tmf calculations, and current family papers.

Spectral-sequence charts retain products and filtrations that an abelian-group table discards. For research use, `data/stable_stems_0_90.csv` should be paired with the IWX Adams charts and their Zenodo data, the Bruner-Rognes Ext database, and machine-proof datasets. A complete multiplication table through 90 has not been published as a single audited object.

# 7. Distinguished classes: Hopf invariant, Kervaire invariant, and image J

## 7.1 The Hopf-invariant-one theorem

The classical Hopf invariant assigns an integer to maps S^{2n-1}-\>S^n. Hopf fibrations give invariant one for n=1,2,4,8. Adams proved these are the only possibilities. Stably, the nontrivial positive-dimensional Hopf-invariant-one classes are η in π_1^S, ν in π_3^S, and σ in π_7^S.

Their orders in the integral stable groups are 2, 24, and 240, respectively. Their 2-primary orders are 2, 8, and 16. These classes generate much of the low-dimensional algebra, but Nishida nilpotence implies each positive-degree class, including η, ν, and σ, becomes zero after sufficiently many products.

## 7.2 Kervaire-invariant-one classes

| **Class**    | **Stem**  | **Description**   | **Status/source**                 |
|--------------|-----------|-------------------|-----------------------------------|
| **θ_1**      | 2         | η^2               | Classical                         |
| **θ_2**      | 6         | ν^2               | Classical                         |
| **θ_3**      | 14        | σ^2               | Classical                         |
| **θ_4**      | 30        | Higher class      | Barratt-Mahowald-Tangora era      |
| **θ_5**      | 62        | Higher class      | Barratt-Jones-Mahowald / Lin / Xu |
| **θ_6**      | 126       | Detected by h_6^2 | Lin-Wang-Xu 2025 preprint         |
| **θ_j, j≥7** | 2^{j+1}-2 | Do not exist      | Hill-Hopkins-Ravenel 2016         |

Browder proved that Kervaire-invariant-one elements can occur only in stems 2^{j+1}-2 and correspond in the Adams spectral sequence to h_j^2. Hill-Hopkins-Ravenel ruled out all j≥7, leaving j=6, stem 126. Lin-Wang-Xu’s current preprint proves h_6^2 survives. Because the last step is still a preprint at the report cutoff, the mathematically accurate formulation is “claimed resolved with a detailed proof and machine-supported companion,” not “long-published theorem.”

The Kervaire problem exemplifies the distinction between detecting one element and computing a stem. The claimed θ_6 settles a yes/no geometric invariant without determining the entire 126-stem.

## 7.3 The stable J-homomorphism

Bott periodicity computes π\_\*(O), and the stable J-homomorphism sends a stable vector bundle clutching function to a framed sphere. Adams computed its image. In positive stems congruent to 0 or 1 modulo 8, the classical image of J has order 2. In stem 4m-1, it is cyclic of order equal to the denominator of B\_{2m}/(4m), where B\_{2m} is a Bernoulli number. It is zero in the other positive congruence classes allowed by Bott periodicity.

Examples are order 24 in stem 3 and order 240 in stem 7. At an odd prime p, the p-primary image in degree 2(p-1)r-1 has order p^{ν_p(r)+1}. The Adams e-invariant detects these classes. Image J supplies an infinite height-one family and a logarithmic lower bound on torsion exponents.

## 7.4 Full v1-periodic homotopy versus image J

At odd primes, positive v1-periodic sphere homotopy is essentially governed by image J. At p=2, the full K(1)-local or v1-periodic contribution also includes classes such as η^2 not literally in the classical image of J. Modern stable tables therefore separate a v1-periodic column from v1-torsion rather than labeling the entire column “image J.”

The K(1)-local sphere can be modeled as the fiber of ψ^q-1 on p-complete K-theory for a topological generator q of Z_p^×, with modifications at p=2. This converts height-one stable stems into p-adic valuations of q^r-1 and explains their rigid periodic arithmetic.

# 8. Chromatic organization of the stable stems

## 8.1 Formal groups and height

Complex-oriented cohomology theories assign formal group laws to tensor products of line bundles. Over a field of characteristic p, one-dimensional formal groups have heights 1,2,... or infinity. Morava K-theory K(n) isolates height n; Morava E-theory E_n is a universal deformation theory near a height-n formal group. The chromatic philosophy decomposes p-local stable homotopy into layers indexed by height.

Height zero is rational homotopy; height one is K-theory and image J; height two is elliptic or modular and is partially seen by tmf; higher heights require increasingly complicated automorphism groups and descent. The sphere contains all heights simultaneously, so chromatic localization provides approximations rather than a finite decomposition.

## 8.2 Nilpotence theorem

Nishida proved directly that every positive-degree element of π\_\*^S is nilpotent. Devinatz-Hopkins-Smith generalized this: a map of finite spectra is smash-nilpotent precisely when every Morava K-theory annihilates it. This transforms a difficult homotopy-ring property into a family of field-valued homology tests.

Nilpotence does not mean scarcity. A class can generate arbitrarily long periodic families after acting on a finite complex, even though its product in the sphere ring eventually vanishes. The distinction between nilpotent sphere elements and periodic self-maps of finite spectra is central to chromatic theory.

## 8.3 Thick subcategories and periodicity

Hopkins-Smith classified thick subcategories of finite p-local spectra: they form the chain C_0⊃C_1⊃C_2⊃..., where C_n consists of spectra of type at least n, meaning K(i)\_\*X=0 for i\<n. Their periodicity theorem gives every type-n finite spectrum a v_n self-map, unique up to iterates in an asymptotic sense.

The theorem guarantees periodic families in the homotopy of finite spectra. Producing sphere classes from them requires additional constructions - boundary maps, root invariants, Greek-letter constructions, transfers, or detection by localized units. This is why periodicity is structural but does not by itself enumerate π\_\*^S.

## 8.4 Chromatic convergence and fracture

For a finite p-local spectrum X, chromatic convergence reconstructs X from its E(n)-localizations L_nX via a homotopy limit. Fracture squares assemble adjacent heights. The monochromatic layer M_nX is the fiber of L_nX-\>L\_{n-1}X and isolates height n. These towers organize both theory and computations.

Convergence is not an explicit algorithm: one must compute local categories, descent spectral sequences, and gluing maps. At height two and small primes, tmf and Morava stabilizer group cohomology provide partial access. At height three and above, even localized sphere groups are known only in restricted ranges and families.

## 8.5 The telescope conjecture

For a type-n finite spectrum with a v_n self-map, one may invert the self-map to form a telescope T(n). Ravenel’s telescope conjecture asserted that localization with respect to T(n) agrees with K(n)-localization, or equivalently that finite and Bousfield chromatic localizations coincide at height n. It is true at heights 0 and 1.

Burklund-Hahn-Levy-Schlank construct K-theoretic counterexamples at every prime and every height at least 2. As of the cutoff, this is an arXiv preprint rather than a journal-published theorem, but it has already changed the conceptual landscape. Periodic families detected T(n)-locally need not exhaust K(n)-local behavior, and unstable Bousfield-Kuhn constructions must keep telescopic and chromatic variants distinct.

## 8.6 Chromatic splitting and unresolved reconstruction

The chromatic splitting conjecture and its refinements predict how L\_{n-1} information sits inside the K(n)-local sphere. Counterexamples and corrections at higher heights show that naive splitting patterns fail. The modern problem is not whether chromatic layers exist, but how complicated their extensions and descent data are.

The failure of the telescope conjecture also affects asymptotic expectations. Burklund’s growth paper identifies a precise strong form of telescope failure that would make the Adams E_2 upper bound essentially sharp. Thus the numerical size of the stable stems is linked to the geometry of chromatic localization.

# 9. Infinite families and periodic phenomena

## 9.1 Height-one families

The image-of-J family is the prototypical infinite family. At odd p, Toda’s α-family lies in stems congruent to -1 modulo 2(p-1), with orders controlled by p-adic valuations. At p=2, Bott periodicity creates an eightfold pattern containing η-, μ-, and J-related classes. The connective image-of-J spectrum j packages these systematically.

Recent synthetic work proves strong detection statements for the unit S-\>j, clarifying that the v1-periodic portion is visible in a manageable target. The remaining stable stems are v1-torsion and contain all height-two and higher phenomena.

## 9.2 Greek-letter families

The Greek-letter construction starts from regular sequences in BP\_\* and boundary maps in generalized Moore spectra. The α-family is height one; β is height two; γ and higher letters reflect higher chromatic layers. Miller-Ravenel-Wilson established broad existence and nontriviality results at suitable primes, while low-prime corrections require detailed differentials and divided Greek-letter variants.

Greek-letter notation is not globally uniform. A symbol may denote an Adams-Novikov class, a chosen homotopy representative, or a divided family member with indeterminacy. Reliable use requires specifying the prime, indexing convention, and detector.

## 9.3 Mahowald families and root invariants

Mahowald’s root invariant uses projective spectra and filtered transfers to raise chromatic height: an input class often has a root invariant represented by a higher-height family. This mechanism predicts β-family representatives from α-classes and height-two families from low Hopf classes. It is powerful but technically delicate because root invariants are cosets and filtered variants can differ from actual homotopy classes.

Mahowald uncertainty principles, as emphasized by Isaksen-Wang-Xu, say informally that high-filtration classes can force differentials or extensions far away in the chart. Computations therefore propagate nonlocally; a missing relation in one stem may obstruct a distant result.

## 9.4 Height two at the prime 2: 192-periodicity

At p=2, the natural periodicity visible through tmf and related spectra is 192 in topological degree. Classical families include powers or translates of κ-bar and modular-discriminant phenomena. Not every 192-periodic sphere class is seen by tmf, and the kernel of the tmf Hurewicz map has become a major source of new families.

Bhattacharya-Bobkova-Quigley identify seven new 192-periodic families that are zero in tmf but nonzero after both T(2)- and K(2)-localization. They also determine new 2-torsion and divisibility properties of known families. Bobkova-Quigley add five simple η-torsion families. Carrick-Davies find families in nineteen residue classes modulo 192, including seven simple 4-torsion and four simple 8-torsion classes, detected by fixed points of tmf under an Atkin-Lehner involution.

## 9.5 Height two at the prime 3

The 3-primary β-family and its products are central height-two phenomena. Oka-Toda and Ravenel established the classical foundations. Recent Carrick-Davies work proves many products in v2-periodic families are nonzero and develops a connective height-two image-of-J analogue. Davies’s analysis of β_1 shows β_1^5 is nonzero while β_1^6 vanishes, illustrating that nilpotence and periodic translation coexist.

The natural modular periodicity at p=3 is often 144. As at p=2, localized periodic families do not automatically determine the integral stable groups in each residue class; hidden extensions and higher-height interference remain.

## 9.6 Higher-height families

At primes large relative to height, Greek-letter and Smith-Toda-complex methods construct v_n-periodic classes for arbitrarily large n. At small primes, the existence of finite type-n complexes and sufficiently structured self-maps is more subtle, and some classical Smith-Toda complexes fail to exist. Nonetheless, nilpotence and periodicity guarantee height-n phenomena in the finite stable category.

The sphere-level problem is to detect those phenomena in the unit. Red-shift in algebraic K-theory, topological automorphic forms, and higher real K-theories offer possible detectors. No complete list of higher-height sphere families is known, and “chromatic redshift produces a class” is generally a research program rather than an automatic theorem.

# 10. Products, Toda brackets, Hurewicz images, and detection

## 10.1 Additive groups do not determine the stable homotopy ring

Two spectral-sequence survivors in adjacent stems may multiply to zero, to a named class, or to a class hidden in higher filtration. Graded commutativity imposes 2-torsion constraints on odd-degree squares but leaves many products undecided. Toda’s composition tables, tmf Hurewicz calculations, and recent periodic-product papers are therefore independent layers of knowledge beyond the additive table in `data/stable_stems_0_90.csv`.

Relations also depend on choices of representatives. Toda brackets are sets with indeterminacy, and a statement that a bracket “contains x” is weaker than a strict equality. Modern computational papers increasingly state explicit choices of lifts and finite-cell complexes so that products become machine-checkable.

## 10.2 Stable Hurewicz homomorphisms

The ordinary stable Hurewicz map from π_k^S to H_k(S;Z) is zero for k\>0 because the sphere spectrum has homology only in degree zero. Useful Hurewicz maps therefore target generalized homology theories such as ko, j, tmf, BP\<n\>, or Morava E-theory. A nonzero image detects a sphere class and often identifies its chromatic height.

The ko/j image captures height one. The 2-primary tmf Hurewicz image, computed by Behrens-Mahowald-Quigley, detects a rich but incomplete set of height-two classes. New families in the kernel show that no single connective theory provides a complete detector.

## 10.3 The Curtis conjecture and spherical classes

The stable adjoint maps π\_\*^S into H\_\*(QS^0;F_2), where Dyer-Lashof operations create an enormous algebra. The Curtis conjecture predicts that, on positive-degree indecomposables, only Hopf-invariant-one and Kervaire-invariant-one classes are spherical. Many partial results bound Adams filtration, primitive length, or families, but the full conjecture remains open.

The conjecture should not be confused with the ordinary stable Hurewicz map to H\_\*(S). It concerns the unstable homology of the infinite loop space QS^0 and is one of the sharpest proposed characterizations of geometrically visible stable classes.

## 10.4 Kahn-Priddy transfer

The transfer Σ^∞ RP^∞\_+ -\> S induces a surjection onto the positive-dimensional 2-primary stable stems. Algebraically, this relates Ext for the sphere to Ext for projective spectra. Geometrically, it converts sphere questions into cell-by-cell questions on RP^∞. Wang-Xu’s 61-stem proof uses an algebraic and geometric Kahn-Priddy mechanism to force the differential d_3(D_3)=B_3.

Balderrama’s 2026 norm-based proof reveals that Kahn-Priddy is a manifestation of a more general multiplicative norm phenomenon and extends it to localized, motivic, and synthetic settings.

## 10.5 Infinite Adams-line families

The Adams 1-line contains h_i candidates; Adams’s theorem kills all but the Hopf classes by differentials. The 2-line contains h_i^2 and the Kervaire problem. The 3-line h_j^3 supports an infinite family of d_4 differentials determined by Burklund-Xu. The 4-line includes the e-family; Li-Li’s 2026 result proves the predicted differential pattern known as the New Doomsday Conjecture for that family.

These results are “all j” theorems inside a fixed filtration, complementary to finite-stem tables. They show how a small algebraic pattern can govern infinitely many potential sphere elements even when the full stems are unknown.

# 11. Global growth, torsion, and nonvanishing

## 11.1 Torsion exponent

For a finite p-group G, the p-exponent is the least p^e annihilating G. Adams vanishing lines gave linear bounds on the exponent of π_k^S(p); bo-resolution and BP\<1\> methods improved the coefficient. Burklund’s theorem removes the linear term: the logarithmic p-exponent grows o(k). This is currently the strongest general qualitative bound.

Image J gives elements of order p^{ν_p(r)+1}, so the exponent is at least logarithmic along suitable stems. No construction is known that systematically produces orders near the sublinear upper bound. Hidden p-extensions in the Adams-Novikov spectral sequence are the only possible source of substantially larger orders.

## 11.2 Rank and total size

The May E_1 page gives log rank_p π_k^S = O((log k)^3), hence rank and group size are subexponential. Burklund proves that the cumulative Adams Ext and Adams-Novikov E_2 ranks actually have exp(Theta((log k)^3)) growth. Differentials might drastically reduce this, but a precise strong telescope-failure scenario would imply the upper bound is essentially sharp.

For unstable p-local groups of a fixed sphere, stable estimates combined with EHP and loop-space arguments yield exp(O((log m)^3)) size bounds in degree m. This is the first general subexponential upper bound, but it is far from the sporadic numerical data.

## 11.3 Vanishing and gaps

Stable vanishing stems occur, but no theorem classifies them. Periodic families imply infinitely many nonzero stems in specified congruence classes. The image of J alone gives nonzero groups in infinitely many stems 0,1,3,7 modulo 8 patterns, and higher chromatic families fill many others.

The stable 61-stem is zero, a result requiring a long differential proof rather than a general vanishing criterion. In contrast, unstable π_m(S^2) and π_m(S^3) never vanish in their positive ranges. This sharp difference cautions against extrapolating stable gaps to fixed spheres.

# 12. Geometric applications

## 12.1 Homotopy spheres and smooth structures

For n≥5, oriented homotopy n-spheres form a finite abelian group Θ_n under connected sum. Kervaire-Milnor relate Θ_n to bP\_{n+1}, the subgroup bounding parallelizable manifolds, and to coker J in π_n^S, with a Kervaire-invariant correction in the relevant congruence class. Thus stable stem computations translate into counts of differentiable structures on topological spheres.

The exact sequence has congruence-dependent form, so it is unsafe to quote a single short exact sequence in every dimension. Practically, one computes image J, coker J, the Kervaire map, and bP orders separately. IWX’s fourth table column performs this assembly through dimension 90 except dimension 4.

## 12.2 Unique smooth structures

Kervaire-Milnor established uniqueness in dimensions 5, 6, and 12. Isaksen proved uniqueness in dimension 56, and Wang-Xu in dimension 61. IWX formulate the conjecture that, among dimensions greater than 4, these are the only spheres with unique smooth structures. Dimension 4 remains outside high-dimensional surgery theory and the smooth four-dimensional Poincare problem is open.

For odd dimensions, Wang-Xu’s 61-stem calculation completes the unique-sphere classification: the only odd-dimensional spheres with unique smooth structure are S^1, S^3, S^5, and S^61. The statement includes low-dimensional differential topology, not only stable stems.

## 12.3 Exotic-sphere detection by chromatic classes

Behrens-Hill-Hopkins-Mahowald use coker J and generalized cohomology to detect exotic spheres in low dimensions. Height-two periodic families yield infinite geometric consequences: Carrick-Davies deduce exotic spheres in every dimension congruent to 72, 144, and 168 modulo 192 under their stated construction.

Recent work on free S^1 and S^3 actions on very exotic spheres reduces geometric classification to explicit products in π\_\*^S, and some cases remain ambiguous precisely because those products are not known. This is a concrete example where the multiplicative frontier, not the additive group, is the obstruction.

## 12.4 Vector fields, immersions, and bundle theory

Adams solved the vector-fields-on-spheres problem: the maximum number of everywhere linearly independent tangent vector fields on S^{n-1} is ρ(n)-1, where ρ is the Radon-Hurwitz function. The proof uses K-theory, Adams operations, and the same height-one structure that computes image J.

Stable stems and J also enter immersion theory through normal invariants and obstruction groups. Pontryagin-Thom translates immersions and framed submanifolds into stable maps; surgery theory then uses stable normal data and L-groups to classify manifolds. Homotopy spheres are the most concentrated instance of this interaction.

## 12.5 Kervaire manifolds and framed geometry

A Kervaire-invariant-one class is represented by a framed manifold whose middle-dimensional mod-2 intersection form has Arf invariant one. The existence dimensions therefore encode exceptional framed manifolds, not merely spectral-sequence survivors. Hill-Hopkins-Ravenel’s nonexistence theorem is a geometric theorem proved through equivariant stable homotopy; the proposed dimension-126 existence proof returns to detailed classical/synthetic Adams computation.

# 13. Algorithms, software, datasets, and machine proofs

## 13.1 Computability versus feasible computation

Brown proved that Postnikov complexes and higher homotopy groups of finite simply connected complexes are algorithmically computable. This positive theorem contrasts with the undecidability of fundamental-group triviality for arbitrary finite complexes. It does not make sphere groups easy: the resulting algorithms are far too expensive for the specialized high-stem calculations in this report.

For fixed homotopy degree, Cadek and collaborators give polynomial-time algorithms for homotopy groups and Postnikov systems of finite 1-connected simplicial sets. They also compute homotopy classes of maps into a sphere in a stable range. When the degree is part of the input, hardness results and representative-size lower bounds show severe complexity.

## 13.2 Effective homology and Kenzo

Effective homology replaces infinite chain complexes, such as loop spaces, with finite effective models connected by reductions. The Kenzo system implements iterated loop spaces, Eilenberg-Mac Lane spaces, spectral sequences, and Whitehead/Postnikov towers. It can compute examples inaccessible to naive simplicial enumeration.

Effective-homology output is complementary to classical named-generator tables. It may determine an abstract group for a specified finite space without identifying that group with Toda’s conventional generators or resolving the global family structure.

## 13.3 Ext and chart computation

Bruner’s minimal resolutions and the Bruner-Rognes database provide Ext_A(F_2,F_2), products, and operations in large ranges. IWX publish classical and C-motivic Adams charts and algebraic Novikov/cofiber-of-tau charts on Zenodo. Guozhen Wang’s morestablestems repository and related code expose machine-readable computations.

SeqSee introduces a JSON schema that separates spectral-sequence mathematics from visualization. This is an important reproducibility step: a chart should be generated from structured classes, products, and differentials rather than maintained as an opaque drawing.

## 13.4 Machine proofs among finite CW spectra

Lin-Wang-Xu’s machine-proof project encodes finite spectra, maps, cofiber sequences, spectral-sequence naturality, and extension constraints. The v2 paper documents 49 CW spectra, 180 maps, and 61 cofiber sequences, while current metadata for the evolving dataset reports larger counts. The safe citation is therefore version-specific.

The machine does not replace mathematical input. Users specify cell complexes, maps, and trusted initial differentials; the solver propagates consequences and proves that alternatives are inconsistent. Human arguments still construct key complexes and identify which machine conclusion settles a homotopy question. The last Kervaire preprint is explicitly a hybrid of machine deductions and ad hoc insight.

## 13.5 Reproducibility requirements for future stem tables

1.  Publish raw Ext and spectral-sequence objects, not only raster charts.

2.  Version every differential and extension, with provenance and correction history.

3.  Separate theorem-proved, machine-derived, assumed, and conjectural relations.

4.  Record generator choices and indeterminacies for Toda brackets and hidden extensions.

5.  Provide tests that recompute additive groups from the E_infinity page and extension data.

6.  Export tables in a stable schema suitable for independent checking and formalization.

Homotopy computations are unusually vulnerable to transcription errors because one wrong differential changes several neighboring stems and products. The 2025 70-71 correction is a model for transparent repair: the authors identify the incorrect differential, state the corrected groups, and retract the associated hidden extension.

# 14. Current frontier and major open problems

| **Problem**                            | **Concrete target**                                                                                                       | **Type**                  |
|----------------------------------------|---------------------------------------------------------------------------------------------------------------------------|---------------------------|
| **Complete stems 84-90**               | Resolve the explicit 2-primary alternatives and audit adjacent hidden extensions.                                         | Finite computation        |
| **Extend the contiguous stable range** | Compute full additive groups and products beyond 90.                                                                      | Finite computation        |
| **Unstable 33-stem**                   | Determine π\_{n+33}(S^n)\_(2) for 10≤n≤27 and clarify n=27.                                                               | Unstable/EHP              |
| **Higher unstable stems**              | Create complete all-sphere p-primary ranges beyond 33, ideally with machine-readable generators.                          | Unstable/EHP              |
| **Last Kervaire publication**          | Independent checking and peer-reviewed publication of the dimension-126 proof.                                            | Foundational verification |
| **Telescope counterexamples**          | Peer-reviewed consolidation and computation of the resulting difference between T(n)- and K(n)-local spheres.             | Chromatic                 |
| **Curtis conjecture**                  | Classify spherical classes in H\_\*(QS^0;F_2).                                                                            | Hurewicz                  |
| **Asymptotic growth**                  | Determine whether stable-stem ranks have exp(Theta((log n)^3)) growth or are much smaller.                                | Global                    |
| **Vanishing stems**                    | Find structural criteria or density results for π_n^S=0.                                                                  | Global                    |
| **Higher-height unit detection**       | Construct and classify v_n-periodic sphere families at heights n≥3.                                                       | Chromatic                 |
| **Multiplication database**            | Audit the stable ring, Toda brackets, and power operations through the computed range.                                    | Computational             |
| **Formal verification**                | Kernel-check the algebraic and finite-spectrum deduction layers without replacing expert mathematics by untrusted tables. | Foundations/software      |

## 14.1 Near-term numerical targets

The clearest finite project is an audited completion of stems 84-90 using synthetic Adams methods and the expanding finite-CW-spectrum machine database. Because the unresolved alternatives are explicit, success can be measured unambiguously. A second target is to push the exact stable range past 90 while retaining complete extension and product provenance.

Unstably, the 33-stem gap is similarly concrete. The challenge is not an unknown theory but a long chain of EHP, Toda bracket, and extension calculations. Modern machine assistance could check group-rank constraints and relation propagation, but the construction of unstable representatives remains substantially geometric.

## 14.2 Structural problems

At height two, the immediate task is to reconcile tmf-visible and tmf-invisible periodic families into a coherent description of the K(2)-local and T(2)-local unit. At higher heights, even the correct detectors and finite resolutions are under construction. The telescope counterexamples mean that one must specify which localization a family inhabits.

The Curtis conjecture, chromatic splitting phenomena, and asymptotic growth ask for qualitative control over infinitely many stems. They are harder than extending a table but may ultimately explain why the tables look as they do.

## 14.3 The role of formalization

The abstract foundations of spectra, generalized cohomology, and spectral sequences are increasingly formalizable, but current sphere computations depend on enormous external Ext datasets and thousands of named relations. A realistic formalization program should first verify data schemas, exact-couple propagation, finite-complex naturality, and extension reconstruction, while treating large Ext computations as separately certified inputs.

The most valuable initial benchmark would not be “formalize all stable stems through 90” as one monolith. It would be a layered certificate: raw chain complexes -\> Ext classes -\> spectral-sequence pages -\> differentials -\> E_infinity groups -\> hidden extensions -\> final additive groups, with each correction localized to a small certificate.

# 15. Chronology of major advances

| **Date**      | **Authors**                                  | **Advance**                                                                                                       |
|---------------|----------------------------------------------|-------------------------------------------------------------------------------------------------------------------|
| **1931**      | Hopf                                         | Hopf fibration and invariant.                                                                                     |
| **1938**      | Freudenthal                                  | Stable range under suspension.                                                                                    |
| **1942-1951** | Whitehead, Pontryagin, Rokhlin               | J-homomorphism, framed geometry, first stable stems.                                                              |
| **1951-1953** | Serre                                        | Spectral sequences, finiteness, rational groups, first p-torsion.                                                 |
| **1953**      | Spanier-Whitehead                            | Stable homotopy category.                                                                                         |
| **1955**      | James                                        | Reduced products and EHP machinery.                                                                               |
| **1958-1962** | Toda                                         | p-primary methods, Toda brackets, complete 19-stem table.                                                         |
| **1958-1966** | Adams                                        | Adams spectral sequence, Hopf invariant one, image J.                                                             |
| **1959**      | Bott                                         | Eightfold/twofold periodicity of classical groups.                                                                |
| **1960-1969** | Kervaire, Kervaire-Milnor, Browder           | Kervaire invariant and exotic spheres.                                                                            |
| **1964**      | May                                          | May spectral sequence.                                                                                            |
| **1967-1969** | Novikov, Quillen                             | Complex cobordism, Adams-Novikov, formal groups.                                                                  |
| **1973**      | Nishida                                      | Nilpotence of positive stable classes.                                                                            |
| **1977**      | Miller-Ravenel-Wilson                        | Periodic Greek-letter families.                                                                                   |
| **1978-1981** | Kahn-Priddy, Lin, Mahowald                   | Transfer methods and bo-resolutions.                                                                              |
| **1979**      | Cohen-Moore-Neisendorfer; Oda                | Odd-prime exponent theorem; unstable 25-31 stems at 2.                                                            |
| **1984-1986** | Ravenel and collaborators                    | Chromatic conjectures and synthesis in the green book.                                                            |
| **1988-1998** | Devinatz-Hopkins-Smith; Hopkins-Smith        | Nilpotence, thick subcategories, periodicity.                                                                     |
| **1990s**     | Kochman, Mahowald, Bruner                    | Computer-assisted stable calculations.                                                                            |
| **1999-2001** | Arone-Mahowald; Bousfield                    | Goodwillie and telescopic unstable homotopy.                                                                      |
| **2010-2019** | Dugger-Isaksen, Isaksen, Gheorghe-Wang-Xu    | Motivic deformation and stable stems through 59.                                                                  |
| **2016**      | Hill-Hopkins-Ravenel                         | Kervaire nonexistence above 126.                                                                                  |
| **2017**      | Wang-Xu; Miyauchi-Mukai                      | 61-stem vanishing; complete unstable 32-stem at 2.                                                                |
| **2020-2023** | Isaksen-Wang-Xu                              | Stable computation through 90 and smooth-structure tables.                                                        |
| **2023-2026** | BHLS; BIX; LWX; BBQ; Carrick-Davies; Yang-Wu | Telescope counterexamples, stem corrections, Kervaire preprint, new periodic families, unstable 33-stem progress. |

# Supplement: comprehensive 2026 expansion beyond stem 90

This supplement upgrades the original low-stem survey into a source-audited state-of-knowledge report. Its central organizing principle is that there is no single computational frontier. A claim about an Ext chart, an Adams E\_∞ page, a p-local additive group, an integral group, a ring presentation, or a chromatic family is a different kind of result and must be labeled separately.

<table>
<colgroup>
<col style="width: 100%" />
</colgroup>
<thead>
<tr class="header">
<th><strong>Interpretive rule<br />
</strong>A finite consecutive table is only one form of knowledge. Beyond stem 90, exact closed formulas, complete odd-primary ranges, isolated high-dimensional classes, periodic congruence families, product theorems, and localized calculations all continue indefinitely. Conversely, an Ext computation or a detected periodic class does not determine the whole stable stem containing it.</th>
</tr>
</thead>
<tbody>
</tbody>
</table>

# S1. Completeness protocol and the actual numerical frontiers

## S1.1 Seven distinct meanings of “computed”

- Algebraic input range: Ext, the Adams-Novikov E_2-term, or a May/algebraic-Novikov chart has been computed.

- Differential range: enough spectral-sequence differentials are known to identify an E_r or E\_∞ page.

- Additive p-local range: the abelian p-primary group is determined, including hidden additive extensions.

- Multiplicative p-local range: products, module actions, and hidden multiplicative extensions are also determined.

- Integral range: all relevant primes have been assembled and cross-prime notation has been reconciled.

- Generator-level range: representatives, Toda brackets, indeterminacies, and spheres of origin are identified.

- Family/localized result: a class or family is proved nonzero, often after T(n), K(n), tmf, or another detector, without classifying its ambient group.

The usual sentence “the stable stems are known through 90” compresses these distinctions. The IWX computation provides a remarkably detailed 2-primary Adams and motivic calculation through 90, but its published table itself enumerates residual alternatives near the top. The 2025 synthetic paper corrects stems 70 and 71 and completes the additive 2-primary groups in stems 82 and 83. Exact integral additive groups therefore stop at stem 83, not 90.

## S1.2 Audited frontier table

Table S1. Distinct numerical and structural frontiers as of 8 August 2026.

| **Object**                             | **Range**                              | **Completeness**                                      | **Resolved information**                                                | **Remaining issue**                                             | **Principal source**                                              |
|----------------------------------------|----------------------------------------|-------------------------------------------------------|-------------------------------------------------------------------------|-----------------------------------------------------------------|-------------------------------------------------------------------|
| Integral stable additive groups        | 0-83                                   | complete                                              | all primes and additive extensions                                      | none in range                                                   | IWX 2023; Burklund-Isaksen-Xu 2025                                |
| Integral stable additive groups        | 84-90                                  | partial                                               | exact in stems 87,88,89; explicit alternatives elsewhere                | 2-primary ambiguities in 84,85,86,90                            | IWX 2023 with BIX corrections                                     |
| 2-primary classical Adams E2           | through stem 110                       | algebraic input range                                 | Ext chart                                                               | does not by itself determine homotopy                           | IWX chart datasets / Bruner-style Ext computations                |
| 2-primary stable homotopy              | through 90, partial higher             | near-complete/partial                                 | low stems plus selected facts into 90s                                  | differentials and hidden extensions                             | IWX 2023; BIX 2025; machine-proof project                         |
| 3-primary stable homotopy              | through 108                            | complete classical computation                        | non-J table plus image J                                                | none in stated range                                            | Tangora/Aubry/Ravenel; Ravenel 2026 Table A3.2                    |
| 5-primary stable homotopy              | through 999                            | complete classical table with source-marked ? entries | non-J elements/relations plus image J                                   | entries explicitly marked ? at 932,933,970,971 in current table | Ravenel 2026 Table A3.3                                           |
| Odd-primary image J                    | all stems                              | closed formula                                        | exact cyclic summands                                                   | none                                                            | Adams; Quillen; Sullivan; Ravenel                                 |
| 2-primary v1-periodic summands         | all stems                              | closed formula                                        | image-J and Adams v1-periodic summands                                  | none                                                            | Adams; Davis-Mahowald; Ravenel                                    |
| 2-primary height-two periodic families | arbitrarily high stems                 | 125 explicit period-192 families in 19 residues       | existence, orders for cataloged simple families, periodicity, detectors | not a classification of all 2-primary stems                     | Carrick-Davies 2025/2026; BBQ; BQ                                 |
| 3-primary height-two products          | arbitrarily high stems                 | large explicit families/products                      | j_2 Hurewicz image and many nonzero products                            | not a complete ring presentation                                | Carrick-Davies arXiv:2410.02564v3                                 |
| Integral unstable k-stems              | k\<=20, all sphere dimensions          | complete                                              | all primes and extensions                                               | none                                                            | Toda 1962; Mimura-Toda 1963                                       |
| 2-primary unstable k-stems             | k\<=32, all sphere dimensions          | complete                                              | groups and classical generators/relations                               | none in range                                                   | Mimura; Mimura-Mori-Oda; Oda; Inoue-Mukai; Miyauchi-Mukai         |
| 2-primary unstable 33-stem             | n=2-9 and stable/backward range n\>=28 | partial                                               | three 2026 extension problems plus previous cases                       | n=10-26 unresolved; n=27 source inconsistency                   | Yang-Wu 2026 and predecessors                                     |
| 3-primary unstable groups              | k\<80 (source convention)              | complete prime-local tables                           | 3-primary groups in Toda monograph range                                | not integral and not all primes                                 | Hirosi Toda, Unstable 3-Primary Homotopy Groups of Spheres (2003) |

## S1.3 Evidence and version policy

Peer-reviewed papers and published monographs are treated as established subject to explicit corrections. A current arXiv proof is labeled “preprint theorem,” even when later authors and Ravenel’s 2026 monograph use it as an input. Machine deductions are credited to the exact dataset/version from which they were generated. Question marks, “or” alternatives, and contradictory captions are not normalized away.

The cutoff matters. Carrick-Davies’ height-two paper grew from 110 families in seventeen residues in its first version to 125 families in nineteen residues in version 2. Their p=3 product paper was revised on 3 August 2026. Ravenel’s third digital edition was updated in 2026 and incorporates the claimed θ_6 result. All counts in this report refer to the latest versions found before 8 August 2026.

# S2. Stable numerical atlas, including all major information beyond stem 90

## S2.1 The integral and 2-primary bottleneck

The exact integral additive group π_k^S is known for every 0≤k≤83. In stems 84-90 the odd-primary pieces are known, and the remaining alternatives are purely 2-primary: one possible Z/2 in stem 84; several additive/extension patterns in stem 85; a Z/2-versus-Z/4 ambiguity in stem 86; and one possible Z/2 in stem 90. Stems 87, 88, and 89 are exact. There is no accepted consecutive integral table immediately after 90 because the 2-primary Adams differentials and hidden extensions are not all resolved.

This does not mean that π_k^S is “unknown” for k\>90. Every such stem has exact height-one summands when the J-formula applies; the complete p=3 component is known through 108; the p=5 calculation reaches 999; finite families and products populate arbitrarily high stems; and the Adams E_2-term extends beyond the range in which the actual homotopy groups have been assembled.

## S2.2 Image of J and the complete height-one pattern in all dimensions

The stable J-homomorphism J:π_k(SO)→π_k^S is completely understood. In degree 4m−1, the order of its image is the denominator of B\_{2m}/(4m), where B\_{2m} is the Bernoulli number, with the low-dimensional conventions incorporated. Prime-locally, for an odd prime p, the p-primary image is

<table>
<colgroup>
<col style="width: 100%" />
</colgroup>
<thead>
<tr class="header">
<th><strong>Odd-primary image-of-J formula<br />
</strong>(im J)_{2(p−1)t−1}[p^∞] ≅ Z/p^{1+ν_p(t)}, and it is zero in the other positive stems. Equivalently, in degree 4m−1 it is nonzero at p exactly when p−1 divides 2m, with order p^{1+ν_p(m)} after the equivalent reparameterization.</th>
</tr>
</thead>
<tbody>
</tbody>
</table>

At p=2 the v_1-periodic part has the familiar 8-fold pattern. In stems 8t−1 it contains a cyclic group of order 2^{ν_2(t)+4}; in positive stems congruent to 0 or 2 mod 8 there is Z/2; in stems congruent to 1 mod 8 there are two Z/2 summands after the initial exceptions; and in stems congruent to 3 mod 8 the periodic summand is Z/8 after the low-dimensional exceptions. The companion file v1_periodic_image_J_0_1000.csv instantiates these closed formulas through stem 1000, but the theorem itself has no upper cutoff.

## S2.3 Complete 3-primary groups through stem 108

Ravenel’s Table A3.2 combines the classical Tangora/Aubry/Ravenel calculation of all non-J classes with the closed image-J formula. The resulting p-local additive groups are complete through stem 108. The portion beyond the usual integral frontier is reproduced below; the full 0-108 ledger is `data/stable_3_primary_groups_0_108.csv`.

**Canonical ledgers:** `data/stable_3_primary_groups_0_108.csv` gives the full additive groups; `data/stable_3_primary_nonJ_classes_0_108.csv` gives named non-J classes, orders, and relations.

Notable features include a cyclic order-nine class x_93 in stem 93; a Z/9 image-J summand in stem 95; and in stem 107 a Z/81 image-J summand together with two independent non-J classes of order three. Complete p-local knowledge here does not resolve the 2-primary component of the same integral stems.

## S2.4 The p=5 computation through the 1000-stem

Ravenel’s 2026 third edition applies the Adams-Novikov and chromatic calculations of Chapter 7 to the p=5 sphere “up to the 1000-stem.” Table A3.3 lists the non-J stable homotopy through stem 999, while the image-J summand is supplied by the closed formula above. The table is exceptionally long because it records named elements, additive multiples, products, and selected Toda-bracket relations rather than only abstract group orders.

<table>
<colgroup>
<col style="width: 100%" />
</colgroup>
<thead>
<tr class="header">
<th><strong>Four preserved source uncertainties<br />
</strong>The current Table A3.3 contains explicit question marks at stems 932, 933, 970, and 971. This report and its CSV retain them. It therefore describes the result as a computation ledger to the 1000-stem, not as an unqualified claim that every class identification and permanence question in 0-999 is resolved.</th>
</tr>
</thead>
<tbody>
</tbody>
</table>

The headline ring-theoretic consequence is β_1^{17}≠0 at p=5 together with the Adams-Novikov differential d\_{33}(γ_3)=β_1^{18}. Consequently the Smith-Toda complex V(3) does not exist at p=5, and V(2) cannot be a ring spectrum. Ravenel conjectures the general p≥7 pattern β_1^{p^2−p}≠0 and β_1^{p^2−p+1}=0, together with a specified higher Toda bracket; this remains open.

## S2.5 Larger primes

Serre’s theorem and the Adams vanishing range imply that the first p-torsion in the stable sphere occurs in stem 2p−3, represented by α_1. Hence a fixed stem k has no p-primary component for p\>(k+3)/2, so assembling an integral stem always involves only finitely many primes. At p≥7 the literature contains image-J classes, alpha families, divided beta and higher Greek-letter classes, Toda-bracket constructions, and substantial localized computations, but no universally cited consecutive complete table analogous to p=3 through 108 or the p=5 Ravenel table. The correct statement is family-by-family rather than “known through N.”

# S3. High-dimensional periodic families and chromatic results

## S3.1 What periodicity proves and what it does not

The Devinatz-Hopkins-Smith nilpotence theorem says that a map of finite spectra is nilpotent exactly when every Morava K-theory sees it as nilpotent. The Hopkins-Smith periodicity theorem supplies v_n self-maps on type-n finite spectra, unique up to powers. Iterating such a map produces periodic families in the homotopy of finite spectra. Obtaining actual classes in π\_\*^S requires a map from or to the sphere and a nonvanishing argument; periodicity alone is not a complete description of the stable stems.

## S3.2 The 2-primary period-192 catalog

At height two and p=2, the natural period is 192, corresponding to v_2^{32}. Bhattacharya-Bobkova-Quigley constructed seven tmf-invisible families in residues 23, 47, 71, 74, 95, 119, and 167 modulo 192 and proved their survival after both T(2)- and K(2)-localization. Bobkova-Quigley isolated five simple η-torsion families in residues 23, 73, 95, 120, and 145.

Carrick-Davies’ current revision gives the largest unified catalog: 125 nonzero periodic families in nineteen residue classes modulo 192. Seven families are simple 4-torsion and four are simple 8-torsion. All vanish under the ordinary tmf-Hurewicz map but are detected by a fixed-point spectrum for an Atkin-Lehner involution. Their geometric corollaries include exotic spheres in dimensions 72, 144, and 168 modulo 192.

**Canonical catalog:** `data/height_two_2_primary_192_periodic_families.csv` records all 26 grouped rows, 125 families, orders, residues, filtration ranges, detectors, and source URLs.

## S3.3 Height two at p=3## S3.3 Height two at p=3

At p=3 the fundamental periodicity is 144. Carrick-Davies construct and analyze a connective height-two image-of-J spectrum j_2, compute the relevant Hurewicz image, and prove that many products among divided beta-family classes are nonzero in arbitrarily high stems; selected Toda brackets are shown not to contain zero. The August 2026 revision makes these product statements one of the strongest available descriptions of the high-dimensional 3-primary stable homotopy ring.

Davies revisits Toda’s β_1^5≠0 and β_1^6=0. For Shimomura’s 144-periodic family {β\_{1+9s}}, every fivefold product is nonzero and every sixfold product is zero, with generalizations to other periodic families. These theorems determine systematic multiplicative behavior far beyond the range of the complete additive p=3 table.

## S3.4 Higher heights and Greek-letter families

The alpha family is height one and is closely related to J. The beta family supplies height-two classes; divided beta elements record divisibility and are central to the p=3 and p=5 calculations. Gamma and higher Greek-letter constructions arise from invariant ideals in BP\_\* and successive connecting homomorphisms. Their existence in the Adams-Novikov E_2-term is algebraic; survival to the sphere is a separate theorem and can fail. The chromatic filtration, root invariants, generalized Moore/Smith-Toda complexes, and topological modular forms organize the known survivors, but no theorem says that a finite collection of Greek-letter families exhausts π\_\*^S.

At every height n there are type-n finite spectra and periodic self-maps. This yields infinitely many chromatic phenomena and, through transfers, root invariants, and finite-resolution constructions, many sphere classes. The specific sphere families become sparser and more conditional as n grows. A complete high-height catalog is not known, and chromatic localization can retain classes that do not lift uniquely to the integral sphere.

# S4. Comprehensive unstable record beyond the stable tables

## S4.1 Exact ranges

Table S4. Complete and partial unstable computation ranges.

| **Prime/scope** | **Stem offset** | **Sphere dimensions**   | **Status**                             | **Primary source**                | **Notes**                                                                                       |
|-----------------|-----------------|-------------------------|----------------------------------------|-----------------------------------|-------------------------------------------------------------------------------------------------|
| integral        | 0-19            | all (Toda table)        | complete                               | Toda 1962                         | Full integral table; stable value included.                                                     |
| integral        | 20              | all                     | complete                               | Mimura-Toda 1963                  | Completes integral 20-stem.                                                                     |
| 2-primary       | 21-22           | all                     | complete                               | Mimura 1965                       |                                                                                                 |
| 2-primary       | 23-24           | all                     | complete                               | Mimura-Mori-Oda 1975              |                                                                                                 |
| 2-primary       | 25-31           | all                     | complete after later corrections       | Oda 1979; Inoue-Mukai             | Generator and extension literature should be consulted for conventions.                         |
| 2-primary       | 32              | all n\>=2               | complete                               | Miyauchi-Mukai 2017               |                                                                                                 |
| 2-primary       | 33              | n=2-9                   | known                                  | Oda; Miyauchi-Mukai; Yang-Wu 2026 |                                                                                                 |
| 2-primary       | 33              | n=10-26                 | open/incomplete                        | Yang-Wu 2026                      |                                                                                                 |
| 2-primary       | 33              | n=27                    | source-internal inconsistency          | Yang-Wu 2026                      | Caption/corollary and prose/table do not agree; report conservatively does not call it settled. |
| 2-primary       | 33              | n\>=28                  | known by backward/stable-range methods | Thomeier + stable 33-stem         |                                                                                                 |
| 3-primary       | k\<80           | Toda monograph coverage | complete prime-local tables            | Toda 2003                         | Independent of the shorter all-prime integral frontier.                                         |
| all primes      | stable range    | n\>=k+2                 | reduces to stable stem                 | Freudenthal                       | Every stable computation gives infinitely many unstable groups.                                 |

Toda’s 1962 Composition Methods gives the integral all-sphere table through k=19, and Mimura-Toda complete k=20. The all-sphere 2-primary record continues through k=32 via Mimura, Mimura-Mori-Oda, Oda, later correction papers, and Miyauchi-Mukai. The 33-stem is the first general 2-primary gap.

## S4.2 The 2-primary 33-stem

Yang-Wu’s 2026 work resolves three previously open extension problems and gives π_39(S^6)\_(2)≅Z/4⊕(Z/2)^6, π_40(S^7)\_(2)≅Z/4⊕(Z/2)^4, and π_41(S^8)\_(2)≅Z/8⊕Z/4⊕(Z/2)^6. Together with earlier work, n=2,...,9 is known. Backward-from-stability arguments determine n≥28. The source’s prose and table disagree about n=27; the conservative status is therefore: n=10,...,26 unresolved and n=27 not safely certified.

## S4.3 Toda’s 3-primary unstable table through the 79-stem

The most important numerical correction to a “Toda only through 19” narrative is Toda’s 2003 monograph Unstable 3-Primary Homotopy Groups of Spheres. It gives complete p=3 tables through k\<80 in its indexing convention, across all sphere dimensions. This is prime-local rather than integral and is logically independent of the shorter all-prime frontier. The source PDF is supplied in the research archive used for this report; generator and relation conventions should be read directly from Toda when a specific unstable class is required.

## S4.4 Uniform structural results for all spheres

- Freudenthal: π\_{n+k}(S^n)→π\_{n+k+1}(S^{n+1}) is an isomorphism for n≥k+2 and surjective for n=k+1. Every stable result therefore determines infinitely many unstable groups.

- Rational homotopy: an odd sphere has only π_n⊗Q≅Q; an even sphere has π_n⊗Q≅Q and π\_{2n−1}⊗Q≅Q, with all other rational groups zero.

- Serre finiteness: apart from those rational summands, the homotopy groups of a sphere are finite. Serre also identifies the first occurrence of odd-primary torsion.

- Hilton-Milnor: loop spaces on wedges of spheres split into products indexed by basic Lie words, reducing many wedge calculations to sphere groups and Whitehead products.

- EHP and James-Hopf invariants: these exact sequences relate neighboring spheres and are the engine behind the low unstable tables and spheres-of-origin questions.

- Cohen-Moore-Neisendorfer: for odd p, strong exponent theorems bound the p-primary torsion of odd-dimensional spheres; the p^n-power map on the relevant loop space is null in the classical range, giving exponent p^n for π\_\*(S^{2n+1})\_(p) in the standard formulation.

- Ivanov-Mikhailov-Wu: π_m(S^2) is nonzero for every m≥2; the Hopf fibration transfers the corresponding nonvanishing to π_m(S^3) for m≥3.

## S4.5 Unstable chromatic and Goodwillie descriptions

The Bousfield-Kuhn functor extracts v_n-periodic unstable homotopy and relates it to T(n)-local stable homotopy. Arone-Mahowald identify layers of the Goodwillie tower of the identity on odd spheres and show that only p-power layers contribute to v_n-periodic homotopy. Kuhn, Behrens, Heuts, and others refine this into a chromatic description of unstable homotopy. These results are structural and often computational after localization, but they do not replace the integral EHP/Toda tables.

# S5. Products, Toda brackets, spectral-sequence families, and Hurewicz detection

## S5.1 The additive table is not the stable homotopy ring

The graded ring π\_\*^S is graded-commutative, and every positive-dimensional element is nilpotent by Nishida. An additive decomposition does not specify products, composition indeterminacy, secondary operations, or Massey/Toda brackets. The IWX charts and Ravenel tables retain much more structure than a list of finite abelian groups; a complete multiplication table through even the low stems has not been published as a single audited object.

Toda brackets are essential because many named generators are most naturally defined as secondary or higher compositions. Their values are cosets with indeterminacy, and equations can change under generator conventions. The source ledgers therefore distinguish abstract group order, named representative, bracket definition, and multiplicative relation.

## S5.2 Infinite Adams differential families

The classical “Doomsday” problem asks whether repeated Sq^0 families in Ext eventually die. Burklund-Xu prove uniform d_4 differentials on h_j^3 for j≥6, while h_j^2 survives to E_5. Li-Li’s 2026 theorem proves the New Doomsday conjecture for the e-family on the Adams 4-line. Together with Adams’ h_j differentials and HHR’s Kervaire result, these are rare uniform theorems controlling an infinite region of the Adams chart rather than a finite stem range.

## S5.3 Hurewicz homomorphisms

Ordinary integral stable homology detects only π_0^S, but generalized Hurewicz maps—to ko, tmf, Morava E-theory, j, j_2, and fixed-point forms of tmf—detect periodic classes. The mod-2 homology H\_\*(Q_0S^0;F_2) contains many primitive classes, very few of which can be spherical. The Curtis conjecture predicts that the positive-dimensional spherical classes are precisely the Hopf-invariant-one and Kervaire-invariant-one classes. Eccles and Lannes-Zarati formulate related geometric and algebraic restrictions.

## S5.4 Transfers and the Kahn-Priddy theorem

The Kahn-Priddy transfer from the stable homotopy of BΣ_p to the p-primary sphere is surjective in positive degrees. At p=2, projective-space filtrations and the Segal conjecture lead to the stable and superstable EHP spectral sequences and the Mahowald invariant. These mechanisms explain why symmetric-group and projective-space calculations repeatedly create sphere classes and why root invariants often increase chromatic height.

## S5.5 Recent generator-level unstable relations

Miyauchi-Mukai’s 2026 preprint proves that the Toda brackets ⟨ν-bar,σ,ν-bar⟩ and ⟨ν,η,σ-bar⟩ are nontrivial, affirming the stated Mahowald conjecture, and determines relations involving ν-bar_6ω_14 in π_30(S^6) and ν-bar_7ω_15 in π_31(S^7). Such results do not enlarge a consecutive additive frontier, but they are indispensable for a complete account of the known composition structure.

# S6. Global theorem families and geometric consequences

## S6.1 Hopf invariant one

Adams proved that a map S^{2n−1}→S^n of Hopf invariant one exists only for n=1,2,4,8. Stably, the positive Hopf-invariant-one classes are η, ν, and σ in stems 1, 3, and 7. This result is simultaneously a theorem about cohomology operations, division algebras, vector fields, and the first Adams filtration line.

## S6.2 Kervaire invariant one

Kervaire-invariant-one classes θ_j lie in stem 2^{j+1}−2. Classical constructions give j=1,...,5, in stems 2,6,14,30,62. Hill-Hopkins-Ravenel prove nonexistence for j≥7. Lin-Wang-Xu’s current preprint proves that h_6^2 is a permanent cycle and produces θ_6 in stem 126. Accordingly, the status table reads: existence in dimensions 2,6,14,30,62; preprint existence in 126; nonexistence thereafter.

## S6.3 Pontryagin-Thom and homotopy spheres

Pontryagin-Thom identifies π_k^S with framed bordism Ω_k^{fr}. Kervaire-Milnor relate the group Θ_n of smooth homotopy n-spheres to bP\_{n+1}, coker J, and the Kervaire invariant. Thus every advance in stable stems can alter the census of exotic smooth structures. Current computations support the conjecture that the only n\>4 with a unique smooth sphere are n=5,6,12,56,61. Height-two period-192 families give infinite congruence classes of exotic and, in related work, very exotic spheres.

## S6.4 Nilpotence, thick subcategories, and chromatic convergence

Nishida nilpotence for π\_\*^S is subsumed by the Devinatz-Hopkins-Smith nilpotence theorem. Hopkins-Smith classify thick subcategories of finite p-local spectra by Morava K-theory height. Chromatic convergence reconstructs a finite p-local spectrum from its chromatic tower. These theorems do not compute individual stems, but they are the strongest known global organization of all stable homotopy information.

## S6.5 Telescope failure and chromatic splitting

The telescope conjecture predicted that finite localization L\_{T(n)} and Bousfield localization L\_{K(n)} agree. It is true at heights 0 and 1. Burklund-Hahn-Levy-Schlank’s preprint constructs K-theoretic counterexamples at every prime and every height n≥2. This makes the distinction between a T(n)-detected family and a complete K(n)-local or integral class essential. Strong formulations of the chromatic splitting conjecture also fail at n=p=2, while weaker split-monomorphism and corrected decomposition statements remain open.

## S6.6 Growth and torsion bounds

Burklund-Senger show that the p-primary exponent of π_n^S grows sublinearly in n and that the p-rank of the Adams E_2-page has exp(Θ((log n)^3)) growth. Combined with vanishing lines, this gives the first general subexponential upper bound on the size of stable stems. Related arguments give exp(O((log m)^3)) upper bounds for the p-primary homotopy of a fixed sphere. No matching unconditional asymptotic for the actual groups is known.

# S7. Credible conjectures, challenged conjectures, and settled historical predictions

A conjecture atlas must distinguish four statuses: genuinely open and broadly credible; open but requiring reformulation; challenged by recent preprints; and historical conjectures now settled or refuted. The following ledger records the strongest precise formulation that could be verified and the evidence level as of the cutoff.

## Conjecture status ledger

The complete 27-entry status-audited ledger is `data/conjecture_status_ledger.csv`. It distinguishes open conjectures, conditional predictions, heuristics, historical conjectures now settled or refuted, challenged claims, and preprint-only theorem claims.

## S7.1 Spherical-class conjectures## S7.1 Spherical-class conjectures

Curtis remains the central prediction: at p=2 the only positive-dimensional spherical classes in H\_\*(Q_0S^0) should come from Hopf- and Kervaire-invariant-one elements. Eccles extends the philosophy to QX, and Lannes-Zarati gives an algebraic Adams-filtration shadow. Computations and vanishing results support these conjectures, but no global proof is known. Odd-primary analogues are less canonically formulated.

## S7.2 EHP, Mahowald, and root-invariant conjectures

Ravenel’s Conjecture 1.5.20 predicts spheres of origin and Hopf invariants for divided alpha classes, but the current edition explicitly records a p=3 exception; only a corrected version is viable. Conjecture 1.5.26 predicts the general EHP differential producing Mahowald’s η_j classes. Conjectures 1.5.32-33 say that Mahowald/root invariants raise Kervaire or Greek-letter height. Low-dimensional examples are compelling, but a uniform theorem is absent.

## S7.3 Multiplicative and Adams-chart conjectures

The New Doomsday conjecture predicts that every nontrivial Sq^0 family in Ext has only finitely many survivors. The h_j, h_j^3, and e-family theorems provide strong evidence, but the general statement is open. Ravenel’s p≥7 β_1 exponent conjecture extrapolates the p=5 computation and is among the clearest finite-form odd-primary ring predictions.

## S7.4 Chromatic localization conjectures

The original telescope conjecture is no longer a credible open conjecture at height at least two if the BHLS preprint is accepted. The weak chromatic splitting conjecture and refined splitting patterns remain central. Redshift predicts that algebraic K-theory raises chromatic height; broad upper bounds and many positive cases are theorems, but the full lower-bound/descent package is open.

## S7.5 Algebraic transfer status

Singer conjectured that the algebraic transfer is injective in all ranks. Rank at most three and many rank-four cases are established. Current preprints by Sum and Phuc claim explicit counterexamples in ranks five and six. Because these claims are recent and computationally delicate, this report labels the original global conjecture “preprint-refuted/challenged,” not settled by a peer-reviewed consensus; any future use should cite the exact rank, degree, software output, and revision.

## S7.6 Exponent, growth, and differential-topology conjectures

Moore’s exponent conjecture relates finite p-primary homotopy exponents of finite simply connected complexes to rational ellipticity. It is proved for many sphere-like and elliptic families but open in general. The unique smooth-sphere and very-exotic-sphere conjectures convert coker-J calculations into global predictions in differential topology. The smooth four-dimensional Poincaré conjecture remains separate from stable-stem technology. Sharp asymptotic growth laws for stable and fixed-sphere homotopy remain largely conjectural.

# S8. What remains genuinely unknown

## S8.1 Finite numerical problems

- Resolve the four remaining additive ambiguities in stems 84, 85, 86, and 90 and audit neighboring hidden products.

- Produce the first fully audited consecutive integral range beyond 90, with raw Ext, differential, and extension provenance.

- Finish the all-sphere 2-primary unstable 33-stem for n=10,...,26 and settle the n=27 source discrepancy.

- Turn Toda’s p=3 k\<80 tables into a modern machine-readable generator-and-relation database without losing indeterminacies.

- Clarify the four question-marked entries in Ravenel’s p=5 table and independently reproduce the long calculation.

- Compute multiplication, Toda brackets, and generalized-Hurewicz images in ranges where the additive groups are already known.

## S8.2 Structural problems

- Determine the actual spherical classes and prove or refute Curtis/Eccles/Lannes-Zarati formulations.

- Understand which chromatic periodic families lift from localization to the integral sphere and how many independent families occur in each residue.

- Find the correct post-counterexample formulation of telescope and chromatic splitting phenomena.

- Establish or refute New Doomsday for arbitrary Sq^0 families.

- Determine sharp torsion exponents and asymptotic rank/size growth for stable stems and fixed spheres.

- Relate higher chromatic classes systematically to exotic spheres, manifold actions, and generalized cohomology obstructions.

## S8.3 Reproducibility and formalization

A modern stem computation should publish machine-readable classes, bidegrees, products, differentials, hidden extensions, generator identifications, source citations, and tests that reconstruct the additive group. The Lin-Wang-Xu finite-CW-spectrum machine and SeqSee schema are important prototypes. Formalization in Lean, Coq, or another proof assistant remains embryonic because the main barrier is not defining homotopy groups but formalizing the spectral-sequence, synthetic, and structured-ring infrastructure together with massive data.

# S9. High-priority 2024-2026 source update

Table S6. Sources most responsible for changing the post-90 and 2026 status picture.

| **Authors**                  | **Year**  | **Work**                                                                        | **Why it matters**                                                        |
|------------------------------|-----------|---------------------------------------------------------------------------------|---------------------------------------------------------------------------|
| Isaksen-Wang-Xu              | 2023      | Stable homotopy groups of spheres: from dimension 0 to 90                       | Peer-reviewed; base low-stem computation with explicit uncertainties.     |
| Burklund-Isaksen-Xu          | 2025      | Classical stable homotopy groups of spheres via F_2-synthetic methods           | Peer-reviewed; completes 82-83 and corrects 70-71.                        |
| Ravenel                      | 2026      | Complex Cobordism and Stable Homotopy Groups of Spheres, digital third edition  | Current monograph; p=3 table through 108 and p=5 computation to 1000.     |
| Lin-Wang-Xu                  | 2025      | On the Last Kervaire Invariant Problem                                          | Preprint theorem for θ_6 in stem 126.                                     |
| Lin-Wang-Xu                  | 2024/2025 | Machine proofs for Adams differentials and extension problems among CW spectra  | Preprint plus dataset; machine-assisted finite-spectrum infrastructure.   |
| Carrick-Davies               | 2025/2026 | On periodic families in the stable stems of height two                          | Preprint v2; 125 period-192 families in nineteen residues.                |
| Bhattacharya-Bobkova-Quigley | 2024      | New infinite families in the stable homotopy groups of spheres                  | Preprint; seven T(2)/K(2)-nonzero period-192 families.                    |
| Bobkova-Quigley              | 2024-2026 | New simple eta-torsion families of elements in the stable stems                 | Preprint v3; five simple eta-torsion families.                            |
| Carrick-Davies               | 2024-2026 | Nonvanishing of products in v_2-periodic families at the prime 3                | Preprint v3; j_2 and high periodic products.                              |
| Davies                       | 2025      | Revisiting the beta_1-action on the 3-primary stable homotopy groups of spheres | Preprint; fivefold nonvanishing and sixfold vanishing.                    |
| Burklund-Hahn-Levy-Schlank   | 2023-2026 | K-theoretic counterexamples to Ravenel’s telescope conjecture                   | Preprint theorem; all primes and heights at least two.                    |
| Burklund-Xu                  | 2025      | The Adams differentials on the h_j^3-family                                     | Peer-reviewed; uniform d_4 family.                                        |
| Li-Li                        | 2026      | The Adams differentials on the e-family                                         | Electronically published in Proc. AMS; New Doomsday for e-family.         |
| Yang-Wu                      | 2026      | 2-primary 33-stem calculations                                                  | Current source for three new extension resolutions and the remaining gap. |
| Miyauchi-Mukai               | 2026      | Relations in the 24-th homotopy groups of spheres                               | Preprint; nontrivial Toda brackets and relations.                         |
| Morris                       | 2026      | Periodic phenomena in stable motivic homotopy theory                            | Current survey of motivic/synthetic periodicity and open problems.        |

`data/source_ledger.csv` contains the full source ledger, including classical foundations and specialized computation papers. The list above is intentionally limited to sources that materially changed the frontier or its interpretation after the standard 0-90 narrative.

