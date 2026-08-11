# Cubical Agda companion formalizations

`SecondBatch.agda` contains the sphere-lattice part of the second maintained
formalization batch.  It is checked in `--safe` mode against
[`agda/cubical`](https://github.com/agda/cubical) commit
`92166033326aa59800a580b428125f3c654b5e45` with Agda 2.8.0.

The new maintained derivations are:

- suspension isomorphisms along the first stable stem;
- the Hopf projection equivalence on homotopy groups in degrees at least three;
- the Hopf-fibration equivalence `πₘ(S³) ≅ πₘ(S²)` for `m ≥ 3`;
- `π₄(S²) ≅ ℤ/2`; and
- the complete family `πₙ₊₁(Sⁿ) ≅ ℤ/2` for `n ≥ 3`.

The file explicitly imports the upstream, machine-checked diagonal, `π₃(S²)`,
and `π₄(S³)` computations.  The second maintained ten-result set counts the
three distinct diagonal declarations (group, generator, and cohomological
identification), the two low-dimensional computations, four local sphere
declarations, and the exact-model Lean circle theorem.  It does not count the
extra Hopf-total-space lemma, numeric instances, or lattice cells.  Run:

```bash
bash scripts/check_cubical_second_batch.sh
```

The checker downloads only a digest-pinned Agda binary and a commit-pinned
Cubical library checkout.  Both live outside the repository under
`$CODEX_SCRATCH_ROOT` (or the CI runner scratch directory).
