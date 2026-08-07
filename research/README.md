# Stable-stem research registry

[`stable-stems.json`](./stable-stems.json) records the classical integral stable
homotopy groups of spheres in stems 0 through 90. It is research-source data for
the benchmark and is intentionally separate from generated manifests and website
data.

## Sources and versioning

The base is Table 1 of:

- Daniel C. Isaksen, Guozhen Wang, and Zhouli Xu, *Stable homotopy groups of
  spheres: from dimension 0 to 90*, Publications mathematiques de l'IHES 137
  (2023), 107-243. DOI
  [`10.1007/s10240-023-00139-1`](https://doi.org/10.1007/s10240-023-00139-1).
  The [publisher-hosted open copy](https://www.numdam.org/articles/10.1007/s10240-023-00139-1/)
  includes the table and its notation.

The following published paper is applied as a field-level supersession:

- Robert Burklund, Daniel C. Isaksen, and Zhouli Xu, *Classical Stable Homotopy
  Groups of Spheres via F_2-Synthetic Methods*, Peking Mathematical Journal
  (2025). DOI
  [`10.1007/s42543-025-00098-y`](https://doi.org/10.1007/s42543-025-00098-y).
  Section 1.2 corrects the 2-primary `v1`-torsion entries in stems 70 and 71;
  Theorem 1.1 completes the 2-primary components in stems 82 and 83.

In particular, the registry uses:

- stem 70, 2-primary: `C2^6 direct-sum C4`;
- stem 71, 2-primary `v1`-torsion: `C2^5 direct-sum C4 direct-sum C8`, in
  addition to the unchanged periodic `C16`;
- stem 82, 2-primary: `C2^6 direct-sum C8`;
- stem 83, 2-primary: `C2^3 direct-sum C8^2`.

The JSON carries source identifiers, DOI/URL metadata, row locators, scoped
supersession rules, and a registry version. Do not regenerate corrected rows from
the 2023 table alone.

## Exactness boundary

After applying the 2025 corrections, stems 0-83 and 87-89 are exact as abstract
additive groups. Four rows retain the alternatives explicitly published in the
2023 source:

| Stem | Number of full-group alternatives | Unresolved part |
| ---: | ---: | --- |
| 84 | 2 | 2-primary `v1`-torsion |
| 85 | 4 | 2-primary additive structure |
| 86 | 2 | 2-primary additive structure |
| 90 | 2 | factor-of-2 ambiguity in the 2-primary component |

These rows have `is_exact: false`. Every item in `alternatives` is a complete
integral group, including the known odd-primary and periodic summands; it is not
merely the uncertain fragment. Stems 87, 88, and 89 are exact.

## Group representation

For an exact row, `group.primary_decomposition` maps each prime to sorted cyclic
prime-power orders. For example,

```json
{"2": [2, 8], "3": [3]}
```

means `C2 direct-sum C8 direct-sum C3`. The mechanically derived
`integral_decomposition` gives the same group in canonical invariant-factor form:
`Z^free_rank direct-sum C_d1 direct-sum ...`, with each `d_i` dividing the next.
`torsion_order` is a decimal string so consumers do not depend on JSON integer
width.

The source's notation `n^j` means `j` copies of `C_n`, not `C_(n^j)`. The registry
contains only abstract additive groups. It does not assert named generators,
products, Toda brackets, Adams filtrations, or spectral-sequence representatives.

## Validation

Basic structural validation can be repeated with:

```sh
jq -e '
  .coverage.row_count == 91 and
  (.stems | length == 91) and
  ([.stems[].stem] == [range(0; 91)]) and
  ([.stems[] | select(.is_exact == false) | .stem] == [84, 85, 86, 90])
' research/stable-stems.json
```

During generation, each primary cyclic order was checked to be a power of its
declared prime, each invariant-factor list was checked for divisibility, and each
torsion order was recomputed from the primary decomposition.
