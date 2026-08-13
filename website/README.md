# Homotopy Groups Lean website

Production: <https://vilin97.github.io/homotopy-groups-lean/>

The public theorem tracker and leaderboard for the benchmark. It is built with
Next.js-compatible React on vinext, exported as static HTML, and deployed with
GitHub Pages.

Generated data under `public/data/` comes only from repository sources of truth:

- `manifests/problems/*.toml` for the theorem tracker;
- `research/stable-stems.json` for the stable-stem map;
- `research/report-data/toda_unstable_stems_0_19.csv` and
  `mimura_toda_unstable_stem_20.csv` for exact low-stem hover values;
- `research/thomeier-unstable.json` for exact integral groups derived from the
  backward-from-stability formulas of Satz 1.1--1.8;
- `research/open-problems.json` for the conjecture registry;
- `research/lattice-coverage.json` and `research/formalizations.json` for the
  audited absolute-degree/stem lattice views, formalized-group index, and
  independent Lean 4 proof overlay;
- append-only `results/*.json` for the contributor leaderboard and its
  problem-by-contributor coverage matrix.

The archived literature-review PDF and its three machine-readable companions
are served from `public/reports/`.

Regenerate and verify data from the repository root:

```bash
python3 scripts/generate_low_stem_lattice.py
python3 scripts/generate_low_stem_lattice.py --check
python3 scripts/generate_thomeier_unstable.py
python3 scripts/generate_thomeier_unstable.py --check
python3 scripts/generate_site_data.py
python3 scripts/generate_site_data.py --check
python3 scripts/generate_report_companions.py
```

Build locally with Node.js 22.13 or newer:

```bash
cd website
npm ci
npm run lint
npm test
```

`npm test` builds the same repository-scoped static artifact that GitHub Pages
deploys and verifies that every hosted asset resolves beneath the project URL.

The mathematical lattice is coverage of the current audited registry of
complete additive groups. Gray means **full integral group not classified in
current registry**; it does not mean that no prime-local component, summand,
element, product, bracket, differential, or periodic family is known. The red
33-stem cell is labeled **Source conflict** because one source has inconsistent
scope statements; it is not evidence for two competing group decompositions.
The two finite display domains have these generated counts:

| View | Exact integral | Alternatives | Exact 2-primary only | Source conflict | Full integral group not classified |
| --- | ---: | ---: | ---: | ---: | ---: |
| 92 by 92 absolute degree | 6,722 | 0 | 276 | 1 | 1,465 |
| 92 by 109 stem | 4,793 | 19 | 276 | 1 | 4,939 |

The deployed client refreshes tracker and leaderboard JSON from the public
GitHub repository, so newly recorded comparator verdicts appear without trusting
hand-edited score data.

## Recording new formalizations

There is no hand-maintained website score or expanded lattice-cell table:

1. A hosted evaluator verdict is appended under `results/`. The submission
   workflow runs `generate_site_data.py`, which derives the ranked rows,
   manifest titles, accepted-result matrix, and tracker status in
   `public/data/leaderboard.json` and `tracker.json`. The resulting
   push triggers the Pages deployment.
2. Mathematical lattice changes start in an audited research registry. The
   Thomeier rule matrix is expanded by `generate_thomeier_unstable.py`, which
   validates 307 exact derived cells and the 118-cell absolute-degree subset,
   canonicalizes the direct-sum groups, and attaches theorem and stable-row
   source locators to every cell.
3. For an audited proof found outside the hosted evaluator, add one record to
   `research/formalizations.json`. If it covers displayed lattice cells, add
   one or more inclusive `cell_ranges` rectangles to its `lattice_overlay`, or
   use `degree_lattice_overlay` for absolute-degree coordinates. The latter
   supports the audited `m<n` region predicate used by sphere connectivity.
   Each coloring overlay must identify its exact witness with a `proof` object
   containing a declaration and source line. The generator validates IDs,
   source SHAs, theorem membership, local declaration lines, range shape,
   domain bounds, and duplicate range coverage before expanding the cells used
   by both lattice views and the formalized-group index. Every expanded cell
   receives its own `proof_declaration` and commit-pinned, line-anchored
   `proof_source` fields.
4. Run `python3 scripts/generate_site_data.py`; CI runs the same command with
   `--check`, so source records and published JSON cannot drift.
