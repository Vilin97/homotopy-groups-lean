# Comprehensive 2026 handoff audit

The source package is preserved byte-for-byte in
[`comprehensive-handoff-2026/`](comprehensive-handoff-2026/). The received ZIP
has SHA-256
`22e2f51ec60f14edf308845dc390475591608ba87f7d840fd11fd61d9b212e87`;
all 16 payload hashes in its `SHA256SUMS.txt` pass. The package's
state-of-knowledge cutoff is 8 August 2026.

The source files are evidence artifacts, not proof certificates. Generated
website data are produced by `scripts/generate_extended_frontiers.py`, which
validates the hashes and table invariants and then applies the corrections
below as an explicit overlay. It never rewrites the source package.

## Scope and website interpretation

The expanded report does **not** extend the complete integral stable-stem table
to 1000. It adds several different kinds of information:

- complete integral additive groups through stem 83, plus exact stems 87--89
  and published alternatives in 84, 85, 86, and 90;
- the degree-zero 3-local group and complete 3-primary torsion components in
  positive stems 1 through 108;
- a 354-row ledger of named non-image-J 5-primary classes and relations
  through stem 999, with source question marks at 932, 933, 970, and 971;
- the all-dimensional image-of-J and height-one formulas, instantiated in
  1,520 rows through stem 1000;
- 125 period-192 2-primary height-two existence families in 19 residue
  classes; and
- status ledgers for unstable ranges, high-dimensional results, sources, and
  27 conjectural or historical claims.

Accordingly, the existing 92 by 91 integral/unstable lattice remains unchanged.
The public site displays the new material in a separate stable-frontier atlas.
A coverage band, a named-class tick, and a periodic-family mark have distinct
meanings. A missing 5-primary ledger row means "no non-J entry listed," not a
zero group; a periodic mark proves class existence, not the ambient group.

The handoff stable 0--90 table agrees semantically with
`stable-stems.json` in every row and every published alternative. Its Toda
0--19 matrix is also cell-for-cell identical to the existing curated
companion after header normalization. The older registries are therefore not
overwritten: they retain richer repository schemas and existing consumers.

## Corrections applied by generated consumers

1. The package links `ravenel.pdf`, an older April 2026 revision, although its
   extended data refer to the digital third edition of 15 June 2026, revised
   31 July 2026 and still explicitly "in the process of being revised."
   Generated consumers link `ravenel3rd.pdf` and describe it as an
   author-maintained digital monograph revision. Direct inspection of that PDF
   confirms the handoff's table numbering: **A3.2** is 3-primary stable
   homotopy excluding image J, **A3.3** is the analogous 5-primary table, and
   **A3.4** is Toda's unstable table through offset 19. The complete 3-primary
   rows combine A3.2 with the image-of-J formula printed immediately before the
   tables.

2. In `v1_periodic_image_J_0_1000.csv`, the row at stem 3, prime 2, says
   `Z/4`. It must be `Z/8`: this is the 2-primary part of
   `pi_3^S = Z/24` and is the low-dimensional value in Isaksen--Wang--Xu,
   Theorem 3.1 and Table 3. The normalized registry corrects that one row.

3. The period-192 CSV assigns one blanket `J_0(3)` detector description to all
   grouped rows. Carrick--Davies Table 1 does not mark `J_0(3)` detection for
   rows 26, 74a, 74b, 122, 170a, 170b, and 170c, representing 19 families.
   Those rows are labeled as nonvanishing by the filtration argument of
   Theorem 5.1, without a `J_0(3)` detection claim. All 125 remain
   `T(2)`- and `K(2)`-locally nonzero by Remark 5.5. The other 106 families
   retain the `J_0(3)` detector label.

4. `source_ledger.csv` assigns Yang--Wu's broader three-group paper to
   *Homology, Homotopy and Applications* 28(1), 67--97 (2026). The primary
   record `arXiv:2406.08621v5` has no journal reference, and that HHA slot is an
   unrelated paper. Generated consumers treat the broader paper as a 2024
   preprint. Yang--Wu's narrower `S^6` extension result is published in HHA
   27(2) (2025), 53--60, DOI `10.4310/HHA.2025.v27.n2.a3`.

5. Twelve p=5 CSV rows are visibly damaged by PDF-to-text extraction: stems
   412, 475, 530, 601, 840, 875, 892, 954, 955, 964, 978, and 990 contain
   detached fragments, page headers, or broken operators. They are quarantined
   pending checked transcription from Table A3.3. These package defects are
   distinct from Ravenel's four source-level question marks. Flattened notation
   throughout also means this is class/relation metadata, not a machine-ready
   additive-group table.

6. The report calls Bhattacharya--Bobkova--Quigley's seven-family paper a
   preprint, but it is published in *Geometry & Topology* 30 (2026),
   2367--2393, DOI `10.2140/gt.2026.30.2367`. Carrick--Davies' p=3 product
   paper is an accepted version to appear in *Advances in Mathematics*, not an
   unqualified preprint. The e-family paper's authors are Runji Li and Yuxuan
   Li, DOI `10.1090/proc/17823`.

7. The 128-row source ledger contains 11 duplicate-work pairs and two repeated
   bibkeys (`BurklundIsaksenXu2025` and
   `BurklundHahnLevySchlank2023`); 115 rows have no URL and 125 have no DOI.
   Generated consumers therefore treat it as a raw provenance inventory, not a
   unique keyed bibliography.

8. `REPORT_CORE.md` contains duplicated Markdown heading text at S3.3 and
   S7.1. The source remains verbatim; the generated HTML report de-duplicates
   only its navigation/rendered headings.

9. The report says Toda's 2003 unstable 3-primary PDF is supplied in the
   archive, but the ZIP contains coverage metadata only, not that PDF or its
   full table. No group statements are generated from that coverage row.

10. The conjecture ledger links the Lannes--Zarati entry to an unrelated
    Walsh--Carleson paper; the correct DOI is
    `10.1016/j.crma.2014.01.013`. Its Moore-conjecture DOI is also invalid;
    generated consumers use `10.1017/S0305004100060916`. Finally, a line-break
    transcription changes Ravenel Conjecture 1.5.26 from the actual
    `d_{2^(j-2)}(nu)=eta_j` to `d_{2^j-2}(nu)=eta_j`; the normalized registry
    uses the formula checked directly in the 31 July edition. The curated
    registry also anchors New Doomsday to Minami's 1995 statement on p. 982,
    DOI `10.2307/2374955`, while retaining Li--Li as progress on the e-family;
    weak chromatic splitting is anchored to Hovey's 1995 Introduction and
    Conjecture 4.2(v), DOI `10.1090/conm/181/02036`, with Beaudry retained as
    evidence against the stronger decomposition.

11. The 27-row conjecture ledger mixes precise open conjectures with refuted
    statements, provisional claims, research programs, conditional scenarios,
    and heuristics. `open-problems.json` assigns every raw row an explicit
    disposition. In particular, it does not promote the vague redshift package,
    the Mahowald uncertainty heuristic, or non-uniform Smith--Toda and growth
    programs to formal conjectures; it separately records the published failure
    of strong chromatic splitting and the preprint-qualified Singer status.

Primary verification links:

- [Ravenel's current digital third edition](https://www.sas.rochester.edu/mth/sites/doug-ravenel/mybooks/ravenel3rd.pdf)
- [Isaksen--Wang--Xu, *Stable homotopy groups of spheres*](https://arxiv.org/abs/2001.04247)
- [Carrick--Davies, version 2](https://arxiv.org/abs/2506.20507)
- [Yang--Wu's broader preprint](https://arxiv.org/abs/2406.08621)

## Lean statement coverage

`HomotopyGroups.StableThreePrimary` now states the exact positive-stem
3-primary groups from 1 through 108 as one finite-indexed theorem family using
Mathlib's genuine `CommGroup.primaryComponent`. Stem zero is excluded because
its `Z_(3)` row is localization of an infinite cyclic group, not a primary
torsion subgroup.

The image-J formula, named 5-primary relations, height-two families, and most
chromatic claims remain tracked as foundation- or registry-blocked targets.
They require the corresponding stable maps, spectra, localizations, products,
or structured class registries; placeholder propositions would not faithfully
state the mathematics.
