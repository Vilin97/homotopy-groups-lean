# Homotopy Groups Lean website

Production: <https://homotopy-groups-lean.lean4lean4.chatgpt.site>

The public theorem tracker and leaderboard for the benchmark. It is built with
Next.js-compatible React on vinext and deployed with OpenAI Sites.

Generated data under `public/data/` comes only from repository sources of truth:

- `manifests/problems/*.toml` for the theorem tracker;
- `research/stable-stems.json` for the stable-stem map;
- append-only `results/*.json` for the leaderboard.

Regenerate and verify data from the repository root:

```bash
python scripts/generate_site_data.py
python scripts/generate_site_data.py --check
```

Build locally with Node.js 22.13 or newer:

```bash
cd website
npm ci
npm run lint
npm test
```

The deployed client refreshes tracker and leaderboard JSON from the public
GitHub repository, so newly recorded comparator verdicts appear without trusting
hand-edited score data.
