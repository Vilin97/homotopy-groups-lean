# Literature-review companion data

These are the three machine-readable companions named in Appendix F of the
archived literature review:

- `stable_stems_0_90.csv` is generated from the audited stable-stem registry;
- `toda_unstable_stems_0_19.csv` is a literal transcription of Appendix B in
  its compact notation (`1` means zero, `infty` means `Z`, `+` is direct sum,
  and `a^r` means `r` copies of `Z/a`);
- `homotopy_spheres_bibliography.bib` contains corrected metadata for the
  principal sources.

Regenerate the files with:

```sh
python3 scripts/generate_report_companions.py
```

The generator also refreshes the byte-identical downloadable copies in
`website/public/reports/`.

Check that the committed companions are current without rewriting them with:

```sh
python3 scripts/generate_report_companions.py --check
```

The CSVs record abstract additive groups only. They do not encode generators,
products, Toda brackets, filtrations, or spectral-sequence representatives.
