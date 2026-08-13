import assert from "node:assert/strict";
import { access, readFile, rm, stat, writeFile } from "node:fs/promises";

const siteUrl = "https://vilin97.github.io/homotopy-groups-lean";
const siteBasePath = "/homotopy-groups-lean";
const output = new URL("../dist/client/", import.meta.url);
const indexUrl = new URL("index.html", output);

const html = await readFile(indexUrl, "utf8");

assert.match(html, /<title>Homotopy Groups Lean<\/title>/);
assert.match(html, /Knowledge lattice/);
assert.match(html, /Stable frontier atlas/);
assert.doesNotMatch(html, /chatgpt\.site/i);
assert.doesNotMatch(html, /integral groups through 1000/i);
assert.doesNotMatch(html, /url\(["']?\/_next\//);

const localReferences = [
  ...html.matchAll(/(?:href|src)="([^"]+)"/g),
].map((match) => match[1]);

for (const reference of localReferences) {
  if (
    reference.startsWith("#") ||
    reference.startsWith("mailto:") ||
    (reference.startsWith("https://") && !reference.startsWith(siteUrl))
  ) {
    continue;
  }

  let pathname;
  if (reference.startsWith(siteUrl)) {
    pathname = new URL(reference).pathname;
  } else if (reference.startsWith(siteBasePath)) {
    pathname = reference.split(/[?#]/, 1)[0];
  } else {
    assert.fail(`unscoped local URL in exported HTML: ${reference}`);
  }

  assert.ok(
    pathname === siteBasePath || pathname.startsWith(`${siteBasePath}/`),
    `local URL escapes the Pages base path: ${reference}`,
  );
  const relative = pathname.slice(siteBasePath.length).replace(/^\//, "");
  const target = relative === "" ? indexUrl : new URL(relative, output);
  await access(target);
}

const rsc = await stat(new URL("index.rsc", output));
assert.ok(rsc.size > 0, "static RSC payload is empty");

for (const relative of [
  "reports/homotopy-groups-of-spheres-literature-review.pdf",
  "reports/stable_stems_0_90.csv",
  "reports/toda_unstable_stems_0_19.csv",
  "reports/homotopy_spheres_bibliography.bib",
  "reports/comprehensive-2026/index.html",
  "reports/comprehensive-2026/REPORT_CORE.md",
  "reports/comprehensive-2026/data/stable_3_primary_groups_0_108.csv",
  "reports/comprehensive-2026/data/stable_5_primary_nonJ_0_999.csv",
  "reports/comprehensive-2026/data/v1_periodic_image_J_0_1000.csv",
  "data/extended-frontiers.json",
  "data/leaderboard.json",
  "data/low-stem-exact.json",
  "data/thomeier-unstable.json",
]) {
  await access(new URL(relative, output));
}

await rm(new URL(".vite", output), { recursive: true, force: true });
await writeFile(new URL(".nojekyll", output), "");
console.log(`Verified GitHub Pages artifact at ${output.pathname}`);
