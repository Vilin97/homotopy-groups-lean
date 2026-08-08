# Homotopy groups of spheres: formalization handoff

**Knowledge cutoff:** 8 August 2026

This archive is the non-redundant, machine-oriented subset of the comprehensive literature-review bundle. It is intended for an agent that will turn mathematical statements into formal declarations and then locate or construct proofs.

## Start here

1. Read `FORMALIZATION_GUIDE.md` for status rules, theorem shapes, and deduplication rules.
2. Read `REPORT_CORE.md` for the mathematical survey and source context.
3. Use the CSV files in `data/` as the canonical dense ledgers.
4. Resolve every theorem candidate against its `status` field and cited primary source before treating it as established.

## What was deliberately omitted

- The PDF and DOCX versions of the report: they duplicate `REPORT_CORE.md`.
- `stable_stems_0_90.csv` from the earlier bundle: it is byte-for-byte identical to the audited copy. The audited copy is included here under the canonical name `data/stable_stems_0_90.csv`.
- The report's dense table appendices: the corresponding CSV files are authoritative and easier to parse.
- Build and typesetting scripts: they do not add mathematical content.
- The BibTeX file: `data/source_ledger.csv` contains the same source inventory in a format better suited to an agent.

## Canonical data files

| File | Rows | Role |
|---|---:|---|
| `data/computation_frontiers_2026.csv` | 14 | Separates Ext, spectral-sequence, additive-group, extension, and integral-completeness frontiers. |
| `data/stable_stems_0_90.csv` | 91 | Audited integral stable additive groups. Stems 0-83 are exact; 84-90 retain explicit ambiguities except exact stems 87-89. |
| `data/stable_3_primary_groups_0_108.csv` | 109 | Exact additive 3-primary components, including image of J, for every stem 0-108. |
| `data/stable_3_primary_nonJ_classes_0_108.csv` | 55 | Named non-J generators, orders, and relations. This supplements rather than duplicates the additive-group ledger. |
| `data/stable_5_primary_nonJ_0_999.csv` | 354 | Ravenel's non-J 5-primary ledger. Four rows retain source question marks; combine with the image-J/v1 ledger for full additive information. |
| `data/v1_periodic_image_J_0_1000.csv` | 1520 | Finite expansion through 1000 of all-dimensional height-one/image-J formulas. The formulas, not the cutoff 1000, are the mathematical theorem. |
| `data/height_two_2_primary_192_periodic_families.csv` | 26 | The 125 catalogued height-two families, grouped into 26 rows and 19 residue classes modulo 192. |
| `data/high_dimensional_results_ledger.csv` | 22 | Navigation index for important results beyond the consecutive low-stem range. Use the underlying detailed ledger or primary source for formalization. |
| `data/toda_unstable_stems_0_19.csv` | 20 | Complete integral unstable table in Toda's compact notation through offset 19. |
| `data/unstable_computation_coverage.csv` | 12 | Exact and partial unstable computation frontiers, including the 20-, 32-, and partial 33-stems and odd-primary ranges. |
| `data/conjecture_status_ledger.csv` | 27 | Open, conditional, settled, refuted, challenged, heuristic, and preprint-claimed statements. These are not all theorem candidates. |
| `data/source_ledger.csv` | 128 | Bibliographic and provenance inventory. |

## Interpretation conventions

- `Z` means the infinite cyclic group; `0` or `1` denotes the trivial group according to the file's documented convention.
- `Z/n` is cyclic of order `n`; `(Z/n)^r` is an `r`-fold direct sum; `+` denotes direct sum in compact group expressions.
- `Z_(p)` denotes the p-local integers, not a finite p-primary group.
- `OR` in a group expression records unresolved alternatives. It must not be normalized to one choice.
- Stable stem `k` means `pi_k^S`; unstable offset `k` means `pi_(n+k)(S^n)`.
- A p-primary component, a p-local group, an image-of-J summand, and a non-J quotient/summand are different objects. Do not conflate them.
- Generator names such as `alpha`, `beta`, `eta`, `nu`, `sigma`, and bracket expressions are source-dependent. Formalize them only after fixing explicit representatives and conventions.

## Status rules

- **Exact/published/peer-reviewed:** suitable as a theorem target, still with primary-source verification.
- **Derived exact ledger:** suitable as a theorem target after checking the derivation, especially the addition of image-J summands.
- **Partial/alternative/question mark:** formalize only the weaker disjunction, bound, existence claim, or explicitly unresolved statement supported by the source.
- **Preprint theorem/claim:** preserve the preprint status. Do not silently promote it to a settled theorem.
- **Open/conditional/heuristic/challenged/refuted:** represent as a named proposition, conjecture record, historical statement, or counterexample theorem as appropriate—not as an established positive theorem.

## Important boundaries

- The package is a literature and data handoff, not a proof corpus.
- Additive group tables do not encode multiplication, Toda brackets, Adams filtration, hidden representatives, or canonical generators.
- The p=5 file excludes image J and contains source-flattened notation; entries marked with `contains_source_question_mark=yes` require direct inspection of Ravenel's table.
- High-dimensional periodic-family results prove specified classes in infinitely many stems; they do not classify the entire groups in those stems.
- The last Kervaire class and all-height telescope counterexamples are labeled according to their preprint status at the cutoff.

`MANIFEST.json` gives file hashes, row counts, column names, and roles. `SHA256SUMS.txt` permits integrity checking.
