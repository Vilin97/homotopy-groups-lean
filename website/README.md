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
  audited evidence lattice and independent Lean/Cubical proof overlay;
- append-only `results/*.json` for the leaderboard.

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
