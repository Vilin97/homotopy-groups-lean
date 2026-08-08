import assert from "node:assert/strict";
import { createHash } from "node:crypto";
import { readFile } from "node:fs/promises";
import test from "node:test";

async function render() {
  const workerUrl = new URL("../dist/server/index.js", import.meta.url);
  workerUrl.searchParams.set("test", `${process.pid}-${Date.now()}`);
  const { default: worker } = await import(workerUrl.href);
  return worker.fetch(
    new Request("http://localhost/", { headers: { accept: "text/html" } }),
    { ASSETS: { fetch: async () => new Response("Not found", { status: 404 }) } },
    { waitUntil() {}, passThroughOnException() {} },
  );
}

test("server-renders the benchmark landing page", async () => {
  const response = await render();
  assert.equal(response.status, 200);
  assert.match(response.headers.get("content-type") ?? "", /^text\/html\b/i);
  const html = await response.text();
  assert.match(html, /<title>Homotopy Groups Lean<\/title>/i);
  assert.match(html, /The known edge of/);
  assert.match(html, /homotopy,/);
  assert.match(html, /The theorem tracker/);
  assert.match(html, /The audited \(n,k\)-plane/);
  assert.match(html, /4,468(?:<!-- -->)? exact integral/);
  assert.match(html, /Lean overlay<\/span><strong>183<\/strong>/);
  assert.match(html, /Lean 2 HoTT · synthetic sphere/);
  assert.match(html, /homotopy-groups-of-spheres-literature-review\.pdf/);
  assert.match(html, /A proof earns its checkmark/);
  assert.match(html, /Leaderboard/);
  assert.doesNotMatch(html, /codex-preview|react-loading-skeleton|Your site is taking shape/i);
});

test("ships complete, synchronized benchmark data, report, and social art", async () => {
  const [trackerText, stemsText, researchStemsText, openProblemsText, researchOpenProblemsText, leaderboardText, image, report, stableCsv, todaCsv, bibliography] = await Promise.all([
    readFile(new URL("../public/data/tracker.json", import.meta.url), "utf8"),
    readFile(new URL("../public/data/stable-stems.json", import.meta.url), "utf8"),
    readFile(new URL("../../research/stable-stems.json", import.meta.url), "utf8"),
    readFile(new URL("../public/data/open-problems.json", import.meta.url), "utf8"),
    readFile(new URL("../../research/open-problems.json", import.meta.url), "utf8"),
    readFile(new URL("../public/data/leaderboard.json", import.meta.url), "utf8"),
    readFile(new URL("../public/og.png", import.meta.url)),
    readFile(new URL("../public/reports/homotopy-groups-of-spheres-literature-review.pdf", import.meta.url)),
    readFile(new URL("../public/reports/stable_stems_0_90.csv", import.meta.url), "utf8"),
    readFile(new URL("../public/reports/toda_unstable_stems_0_19.csv", import.meta.url), "utf8"),
    readFile(new URL("../public/reports/homotopy_spheres_bibliography.bib", import.meta.url), "utf8"),
  ]);
  const tracker = JSON.parse(trackerText);
  const stems = JSON.parse(stemsText);
  const researchStems = JSON.parse(researchStemsText);
  const openProblems = JSON.parse(openProblemsText);
  const researchOpenProblems = JSON.parse(researchOpenProblemsText);
  const leaderboard = JSON.parse(leaderboardText);
  assert.equal(tracker.schema_version, 2);
  assert.equal(leaderboard.schema_version, 2);
  assert.equal(tracker.problem_count, tracker.entries.length);
  assert.ok(tracker.problem_count >= 118);
  assert.equal(stems.stems.length, 91);
  assert.deepEqual(stems, researchStems);
  assert.deepEqual(stems.stems.filter((row) => !row.is_exact).map((row) => row.stem), [84, 85, 86, 90]);
  assert.deepEqual(openProblems, researchOpenProblems);
  assert.equal(openProblems.conjectures.length, 7);
  assert.equal(openProblems.conjectures.filter((row) => row.lean.status === "statement_available").length, 2);
  assert.ok(Number.isInteger(leaderboard.accepted_eligible_results));
  assert.ok(Array.isArray(leaderboard.entries));
  for (const entry of leaderboard.entries) {
    assert.ok(Number.isInteger(entry.rank) && entry.rank > 0);
    assert.ok(typeof entry.actor === "string" && entry.actor.length > 0);
    assert.ok(Number.isInteger(entry.solved) && entry.solved > 0);
  }
  assert.ok(image.byteLength > 100_000);
  assert.equal(
    createHash("sha256").update(report).digest("hex"),
    "749a0686118c9e4454b6166da0966b8097ba7ebaf2177db198bacd1f7953f9e6",
  );
  assert.equal(stableCsv.trim().split("\n").length, 92);
  assert.equal(todaCsv.trim().split("\n").length, 21);
  assert.match(bibliography, /Bousfield1985/);
  assert.match(bibliography, /InoueMiyauchiMukai2015/);
});
