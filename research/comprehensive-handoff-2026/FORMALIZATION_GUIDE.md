# Formalization guide

## 1. Separate the kinds of statement

Do not model the literature as one flat list. Use distinct declaration families.

### A. Additive group calculations

Typical mathematical shape:

```text
pi_k^S ≅ A
(pi_k^S)[p^∞] ≅ A_p
pi_(n+k)(S^n) ≅ A
```

The exact Lean formulation depends on the available homotopy-group API. Prefer an additive-group isomorphism to a bare equality. Record whether the statement is integral, p-local, p-complete, or about the finite p-primary subgroup.

### B. Distinguished classes and relations

Typical shape:

```text
exists x : pi_k^S, orderOf x = m
x ≠ 0
m • x = 0
x * y = z
z ∈ todaBracket x y w
```

Generator names are not definitions. Before using a name, fix a construction or a detector that identifies the class and state any indeterminacy.

### C. Infinite and periodic families

Typical shape:

```text
forall j : Nat, exists x_j : pi_(a + period*j)^S, x_j ≠ 0
forall j, orderOf x_j = m
periodicity_map x_j = x_(j+1)
```

A residue-class existence theorem is weaker than a complete calculation of every stem in that residue class. Keep detector, order, filtration, and publication status as separate fields.

### D. Structural theorems

Examples include Freudenthal stabilization, Serre finiteness, rational calculations, image J, Hopf invariant one, nilpotence, thick subcategories, chromatic convergence, exponent bounds, and Pontryagin-Thom. These should be formalized from their mathematical definitions, not generated from CSV rows.

### E. Conjectures and historical statements

Give conjectures a proposition-valued declaration or metadata record, but do not attach a theorem proof. For a refuted conjecture, formalize the original proposition separately from the counterexample/result that refutes it. For a preprint claim, preserve the exact claim and provenance.

## 2. Source-of-truth hierarchy

1. Primary paper or monograph cited in the row.
2. Canonical detailed CSV ledger in this package.
3. `REPORT_CORE.md` narrative summary.
4. `data/high_dimensional_results_ledger.csv` and `data/computation_frontiers_2026.csv` as navigation indexes.

The index files are intentionally concise and should not override a detailed row or primary source.

## 3. Deduplication rules

- `stable_stems_0_90.csv` is the only low-stem additive table in the package.
- `stable_3_primary_groups_0_108.csv` gives the full additive 3-primary group. Do not add image J to it again.
- `stable_3_primary_nonJ_classes_0_108.csv` supplies named classes and relations; it is not a second additive-group table.
- `stable_5_primary_nonJ_0_999.csv` excludes image J. For an additive 5-primary statement, combine it with the applicable row/formula from `v1_periodic_image_J_0_1000.csv`, subject to source-marked uncertainties.
- `v1_periodic_image_J_0_1000.csv` is an instantiated range of all-dimensional formulas. Formalize the formula once; generated corollaries for individual stems are optional.
- `high_dimensional_results_ledger.csv` summarizes results represented in the survey or specialized family ledgers. Use it to find targets, not to generate duplicate declarations.
- `source_ledger.csv` is provenance metadata, not mathematical content.

## 4. Machine-generation policy

A safe CSV-to-Lean generator should:

1. Parse and validate the `status` column before emitting a declaration.
2. Refuse exact theorem generation for any row containing `OR`, `?`, `partial`, `open`, `heuristic`, `conditional`, `challenged`, `refuted`, or `preprint`, unless the mode explicitly requests propositions or status-tagged placeholders.
3. Parse compact finite-abelian-group expressions into a normalized direct-sum AST rather than emitting raw strings.
4. Preserve the distinction between `Z`, `Z_(p)`, and finite cyclic groups.
5. Emit provenance in docstrings or a separate metadata structure.
6. Keep source notation for named classes as metadata until representatives are formalized.
7. Generate a coverage test: every exact row is emitted once, every non-exact row is skipped or represented in an explicitly weaker form, and no two source rows generate the same declaration name.

A minimal expression grammar for the additive tables is:

```text
group := 0 | Z | Z_(p) | Z/n | (Z/n)^r | group + group | group OR group
```

Real files contain compact formatting variations, so normalize whitespace, parentheses, and exponent notation before parsing.

## 5. Recommended implementation order

1. **Audit the existing library:** identify definitions of spheres, pointed homotopy groups, suspension, stabilization, spectra, localization, finite abelian groups, and group exponent/order.
2. **Fix notation and equivalence types:** decide how stable groups and p-primary components will be represented.
3. **Formalize global definitions and easy structural statements:** these provide the vocabulary needed by numerical declarations.
4. **Generate exact low-dimensional additive statements:** begin with unambiguous rows from `stable_stems_0_90.csv`; keep the four partial stems separate.
5. **Add exact 3-primary statements:** the full-group table is uniform and status-clean.
6. **Add image-J/v1 formulas:** formalize the all-dimensional theorem before thousands of instantiated corollaries.
7. **Treat p=5 carefully:** formalize the non-J ledger and image-J contribution separately; quarantine the four source-question rows.
8. **Add unstable statements:** Toda's table first, followed by coverage declarations and selected higher prime-local ranges.
9. **Add periodic-family existence theorems:** model residue, period, order, detector, and nonvanishing explicitly.
10. **Add conjecture and provenance records:** these should never be mixed with proved declarations.

## 6. Suggested metadata for each target

```text
id
informal_statement
formal_statement
scope: stable | unstable
prime_scope: integral | p-local | p-primary | rational
stem_or_family
result_kind: group_iso | element | relation | family | structural | conjecture
status: exact | partial | preprint | open | refuted | historical
source_bibkey
source_locator: theorem/table/page/row
generator_convention
formalization_dependencies
notes
```

This metadata prevents a formal statement from losing the qualifications that make it mathematically correct.

## 7. Highest-value initial targets

For a statement-collection project, the best first targets are:

- Freudenthal stabilization and the stable-range identification.
- Serre finiteness/rational sphere homotopy statements.
- Hopf-invariant-one classification.
- The image-of-J order formula.
- Exact low stable stems with no ambiguity.
- Exact 3-primary additive groups through 108 as generated declarations.
- Toda's stable-range consequences from the unstable table.
- Periodic-family nonvanishing statements with simple order claims.

The full chromatic classification machinery, named Toda-bracket relations, and generator-level p=5 transcription are substantially harder because they require much more infrastructure and convention management.
