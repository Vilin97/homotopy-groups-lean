import assert from "node:assert/strict";
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
  assert.match(html, /mapped\./);
  assert.match(html, /Knowledge lattice/);
  assert.match(html, /Lean verified/);
  assert.match(html, /Fully known/);
  assert.match(html, /Some information/);
  assert.match(html, /Uncharted/);
  assert.match(html, /Proof queue/);
  assert.match(html, /Comparator/);
  assert.match(html, /Leaderboard/);
  assert.doesNotMatch(html, /codex-preview|react-loading-skeleton|Your site is taking shape/i);
});

test("ships complete generated benchmark data and social art", async () => {
  const [trackerText, stemsText, openProblemsText, leaderboardText, image] = await Promise.all([
    readFile(new URL("../public/data/tracker.json", import.meta.url), "utf8"),
    readFile(new URL("../public/data/stable-stems.json", import.meta.url), "utf8"),
    readFile(new URL("../public/data/open-problems.json", import.meta.url), "utf8"),
    readFile(new URL("../public/data/leaderboard.json", import.meta.url), "utf8"),
    readFile(new URL("../public/og-lattice.png", import.meta.url)),
  ]);
  const tracker = JSON.parse(trackerText);
  const stems = JSON.parse(stemsText);
  const openProblems = JSON.parse(openProblemsText);
  const leaderboard = JSON.parse(leaderboardText);
  assert.equal(tracker.schema_version, 2);
  assert.equal(leaderboard.schema_version, 2);
  assert.equal(tracker.problem_count, tracker.entries.length);
  assert.ok(tracker.problem_count >= 118);
  assert.equal(tracker.entries.filter((row) => row.formalization_status === "comparator_verified").length, 1);
  assert.equal(stems.stems.length, 91);
  assert.deepEqual(stems.stems.filter((row) => !row.is_exact).map((row) => row.stem), [84, 85, 86, 90]);
  assert.equal(openProblems.conjectures.length, 6);
  assert.equal(openProblems.conjectures.filter((row) => row.lean.status === "statement_available").length, 2);
  assert.ok(Number.isInteger(leaderboard.accepted_eligible_results));
  assert.ok(Array.isArray(leaderboard.entries));
  for (const entry of leaderboard.entries) {
    assert.ok(Number.isInteger(entry.rank) && entry.rank > 0);
    assert.ok(typeof entry.actor === "string" && entry.actor.length > 0);
    assert.ok(Number.isInteger(entry.solved) && entry.solved > 0);
  }
  assert.ok(image.byteLength > 100_000);
});
