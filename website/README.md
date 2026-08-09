# Homotopy Groups Lean website

Production: <https://vilin97.github.io/homotopy-groups-lean/>

The public theorem tracker and leaderboard for the benchmark. It is built with
Next.js-compatible React on vinext, exported as static HTML, and deployed with
GitHub Pages.

Generated data under `public/data/` comes only from repository sources of truth:

- `manifests/problems/*.toml` for the theorem tracker;
- `research/stable-stems.json` for the stable-stem map;
- `research/open-problems.json` for the conjecture registry;
- `research/lattice-coverage.json` and `research/formalizations.json` for the
  audited evidence lattice, formalized-group index, and independent Lean
  overlay;
- append-only `results/*.json` for the contributor leaderboard and its
  problem-by-contributor coverage matrix.

The archived literature-review PDF and its three machine-readable companions
are served from `public/reports/`.

Regenerate and verify data from the repository root:

```bash
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

The deployed client refreshes tracker and leaderboard JSON from the public
GitHub repository, so newly recorded comparator verdicts appear without trusting
hand-edited score data.

## Recording new formalizations

There is no hand-maintained website score or lattice table:

1. A hosted evaluator verdict is appended under `results/`. The submission
   workflow runs `generate_site_data.py`, which derives the ranked rows,
   manifest titles, accepted-result matrix, and tracker status in
   `public/data/leaderboard.json` and `tracker.json`. The resulting
   push triggers the Pages deployment.
2. For an audited proof found outside the hosted evaluator, add one record to
   `research/formalizations.json`. If it covers displayed lattice cells, add
   one or more inclusive `cell_ranges` rectangles to its `lattice_overlay`.
   The generator validates IDs, source SHAs, range shape, domain bounds, and
   duplicate range coverage before expanding the cells used by both the lattice and the
   formalized-group index.
3. Run `python3 scripts/generate_site_data.py`; CI runs the same command with
   `--check`, so source records and published JSON cannot drift.
