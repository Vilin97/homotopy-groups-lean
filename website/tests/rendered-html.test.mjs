import assert from "node:assert/strict";
import { createHash } from "node:crypto";
import { readFile } from "node:fs/promises";
import test from "node:test";

async function render() {
  return readFile(new URL("../dist/client/index.html", import.meta.url), "utf8");
}

test("statically exports the benchmark landing page", async () => {
  const html = await render();
  assert.match(html, /<title>Homotopy Groups Lean<\/title>/i);
  assert.match(html, /mapped\./);
  assert.match(html, /Stable frontier atlas/);
  assert.match(html, /Knowledge lattice/);
  assert.match(html, /Proof queue/);
  assert.match(html, /manifests\/problems\/complexProjectiveSpace_higher_homotopy_mulEquiv_sphere\.toml/);
  assert.doesNotMatch(html, /manifests\/problems\/[^"]+\.json/);
  assert.match(html, /6,604(?:<!-- -->)? exact integral/);
  assert.match(html, /Lean overlay<\/span><strong>4369<\/strong>/);
  assert.match(html, /4,369(?:<!-- -->)? purple cells/);
  assert.match(html, /1 ≤ m &lt; n/);
  assert.match(html, /Lean 4 · kernel checked · exact metric model/);
  assert.match(html, /Exact Lean theorem/);
  assert.match(html, /Submission\.sphere_lower_positive_homotopy_mulEquiv_punit/);
  assert.match(html, /hover to preview · click to pin/i);
  assert.match(html, /Hover preview on/);
  assert.match(html, /research\/open-problems\.md/);
  assert.match(html, /homotopy-groups-of-spheres-literature-review\.pdf/);
  assert.match(html, /reports\/comprehensive-2026\//);
  assert.match(html, /3-local degree 0/);
  assert.match(html, /Comparator/);
  assert.match(html, /Leaderboard/);
  assert.match(html, /π<sub>k<\/sub>\(𝕊\)/);
  assert.doesNotMatch(html, /π<sub>k<\/sub><sup>S<\/sup>/);
  assert.match(html, /Which homotopy groups are in Lean\?/);
  assert.doesNotMatch(html, /Lean 2 HoTT/);
  assert.match(html, /A path-connected space has trivial zeroth homotopy group/);
  assert.doesNotMatch(html, /codex-preview|react-loading-skeleton|Your site is taking shape/i);
  assert.doesNotMatch(html, /integral groups through 1000/i);
});

test("scopes every hosted asset to the GitHub Pages project", async () => {
  const html = await render();
  assert.match(
    html,
    /https:\/\/vilin97\.github\.io\/homotopy-groups-lean\/_next\/static\//,
  );
  assert.match(
    html,
    /href="\/homotopy-groups-lean\/reports\/homotopy-groups-of-spheres-literature-review\.pdf"/,
  );
  assert.match(
    html,
    /href="\/homotopy-groups-lean\/reports\/comprehensive-2026\/"/,
  );
  assert.doesNotMatch(html, /chatgpt\.site/i);
  assert.doesNotMatch(html, /(?:href|src)="\/(?!homotopy-groups-lean(?:\/|"))/);
  assert.doesNotMatch(html, /url\(["']?\/_next\//);
  await readFile(new URL("../dist/client/.nojekyll", import.meta.url));
});

test("ships complete, synchronized benchmark data, reports, and social art", async () => {
  const [trackerText, stemsText, researchStemsText, openProblemsText, researchOpenProblemsText, leaderboardText, frontierText, image, report, stableCsv, todaCsv, bibliography, comprehensiveIndex, comprehensiveReport, researchComprehensiveReport] = await Promise.all([
    readFile(new URL("../public/data/tracker.json", import.meta.url), "utf8"),
    readFile(new URL("../public/data/stable-stems.json", import.meta.url), "utf8"),
    readFile(new URL("../../research/stable-stems.json", import.meta.url), "utf8"),
    readFile(new URL("../public/data/open-problems.json", import.meta.url), "utf8"),
    readFile(new URL("../../research/open-problems.json", import.meta.url), "utf8"),
    readFile(new URL("../public/data/leaderboard.json", import.meta.url), "utf8"),
    readFile(new URL("../public/data/extended-frontiers.json", import.meta.url), "utf8"),
    readFile(new URL("../public/og.png", import.meta.url)),
    readFile(new URL("../public/reports/homotopy-groups-of-spheres-literature-review.pdf", import.meta.url)),
    readFile(new URL("../public/reports/stable_stems_0_90.csv", import.meta.url), "utf8"),
    readFile(new URL("../public/reports/toda_unstable_stems_0_19.csv", import.meta.url), "utf8"),
    readFile(new URL("../public/reports/homotopy_spheres_bibliography.bib", import.meta.url), "utf8"),
    readFile(new URL("../public/reports/comprehensive-2026/index.html", import.meta.url), "utf8"),
    readFile(new URL("../public/reports/comprehensive-2026/REPORT_CORE.md", import.meta.url)),
    readFile(new URL("../../research/comprehensive-handoff-2026/REPORT_CORE.md", import.meta.url)),
  ]);
  const tracker = JSON.parse(trackerText);
  const stems = JSON.parse(stemsText);
  const researchStems = JSON.parse(researchStemsText);
  const openProblems = JSON.parse(openProblemsText);
  const researchOpenProblems = JSON.parse(researchOpenProblemsText);
  const leaderboard = JSON.parse(leaderboardText);
  const frontier = JSON.parse(frontierText);
  assert.equal(tracker.schema_version, 2);
  assert.equal(leaderboard.schema_version, 2);
  assert.equal(tracker.problem_count, tracker.entries.length);
  assert.ok(tracker.problem_count >= 127);
  for (const problemId of [
    "homotopyGroup_change_basepoint",
    "homotopyGroup_homotopy_invariance",
    "homotopyGroup_loop_shift",
    "homotopyGroup_product",
    "pi1_hSpace_mul_comm",
    "pi1_realProjectiveSpace_mulEquiv_zmod_two",
    "realProjectiveSpace_higher_homotopy_mulEquiv_sphere",
  ]) {
    assert.equal(
      tracker.entries.find((entry) => entry.id === problemId)?.knowledge_status,
      "formalized_local",
    );
  }
  assert.equal(stems.stems.length, 91);
  assert.deepEqual(stems, researchStems);
  assert.deepEqual(stems.stems.filter((row) => !row.is_exact).map((row) => row.stem), [84, 85, 86, 90]);
  assert.deepEqual(openProblems, researchOpenProblems);
  assert.equal(openProblems.conjectures.length, 16);
  assert.equal(openProblems.conjectures.filter((row) => row.lean.status === "statement_available").length, 2);
  assert.equal(openProblems.conjectures.filter((row) => row.lean.status === "blocked_on_foundations").length, 14);
  assert.equal(frontier.display.last_stem, 1000);
  assert.equal(frontier.integral.stems.length, 91);
  assert.equal(frontier.three_primary.stems.length, 109);
  assert.equal(frontier.three_primary.stems[0].scope, "3_local_degree_zero");
  assert.deepEqual(
    frontier.three_primary.coverage.positive_stem_primary_components,
    { first: 1, last: 108, status: "exact" },
  );
  assert.equal(frontier.three_primary.stems[91].group, "(Z/3)^3");
  assert.equal(frontier.three_primary.stems[96].group, "0");
  assert.equal(frontier.five_primary_non_j.entry_count, 354);
  assert.deepEqual(frontier.five_primary_non_j.uncertain_stems, [932, 933, 970, 971]);
  assert.equal(
    frontier.five_primary_non_j.entries.find((row) => row.stem === 932).uncertain,
    true,
  );
  assert.deepEqual(
    frontier.five_primary_non_j.quarantined_transcription_stems,
    [412, 475, 530, 601, 840, 875, 892, 954, 955, 964, 978, 990],
  );
  assert.equal(frontier.image_j_v1.ledger.row_count, 1520);
  assert.equal(frontier.image_j_v1.ledger.last, 1000);
  const stemThree = frontier.image_j_v1.stems.find((row) => row.stem === 3);
  assert.ok(stemThree.entries.some((row) => row.prime === "2" && row.group === "Z/8"));
  assert.equal(frontier.height_two_two_primary.grouped_row_count, 26);
  assert.equal(frontier.height_two_two_primary.family_count, 125);
  assert.equal(frontier.height_two_two_primary.residue_count, 19);
  assert.ok(Number.isInteger(leaderboard.accepted_eligible_results));
  assert.ok(Array.isArray(leaderboard.entries));
  assert.ok(Array.isArray(leaderboard.accepted_problems));
  assert.ok(leaderboard.accepted_problems.length >= 6);
  assert.ok(leaderboard.accepted_problems.every((problem) => typeof problem.title === "string" && problem.title.length > 0));
  assert.ok(leaderboard.accepted_problems.some((problem) => problem.title === "The fundamental group of the circle is the integers" && problem.score_eligible === false));
  assert.equal(leaderboard.formalization_inventory.records.length, 45);
  assert.equal(leaderboard.formalization_inventory.lattice.cell_count, 200);
  assert.equal(leaderboard.formalization_inventory.degree_lattice.cell_count, 4369);
  for (const lattice of [
    leaderboard.formalization_inventory.lattice,
    leaderboard.formalization_inventory.degree_lattice,
  ]) {
    assert.ok(lattice.cells.every((cell) =>
      typeof cell.proof_declaration === "string" &&
      cell.proof_declaration.startsWith("Submission.") &&
      /^https:\/\/github\.com\/Vilin97\/homotopy-groups-lean\/blob\/[0-9a-f]{40}\/.+#L[1-9][0-9]*$/.test(cell.proof_source),
    ));
  }
  assert.ok(
    leaderboard.formalization_inventory.records.every((record) =>
      record.system.startsWith("Lean 4")),
  );
  assert.ok(
    leaderboard.formalization_inventory.lattice.cells.every((cell) =>
      cell.n === 1 || cell.k === 0),
  );
  assert.equal(
    leaderboard.formalization_inventory.degree_lattice.cells.filter((cell) => cell.m < cell.n).length,
    4186,
  );
  assert.ok(
    leaderboard.formalization_inventory.degree_lattice.cells.some((cell) =>
      cell.n === 92 && cell.m === 91 &&
      cell.record_id === "lean4-displayed-lower-connectivity"),
  );
  assert.ok(
    leaderboard.formalization_inventory.lattice.cells.some((cell) =>
      cell.k === 0 && cell.record_id === "lean4-benchmark-metric-circle-pi1"),
  );
  assert.ok(
    leaderboard.formalization_inventory.lattice.cells.some((cell) =>
      cell.n === 2 && cell.k === 0 &&
      cell.record_id === "lean4-benchmark-metric-sphere-pi2"),
  );
  assert.ok(
    leaderboard.formalization_inventory.lattice.cells.some((cell) =>
      cell.n === 92 && cell.k === 0 &&
      cell.record_id === "lean4-first-nonvanishing-hurewicz-isomorphism" &&
      cell.proof_declaration === "Submission.sphere_diagonal_homotopy_mulEquiv_int"),
  );
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
  assert.match(comprehensiveIndex, /Repository audit overlay/);
  assert.match(comprehensiveIndex, /Read the correction log/);
  assert.match(comprehensiveIndex, /Formalization-Oriented Research Survey/);
  assert.deepEqual(comprehensiveReport, researchComprehensiveReport);
});
