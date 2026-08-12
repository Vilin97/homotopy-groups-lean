"use client";

import { useEffect, useMemo, useState } from "react";
import initialLeaderboard from "../public/data/leaderboard.json";

type Leader = {
  rank: number;
  actor: string;
  solved: number;
  firsts: number;
  models: string[];
  problems: string[];
};

type AcceptedProblem = {
  id: string;
  title: string;
  family: string;
  score_eligible: boolean;
  first_actor: string | null;
  actors: string[];
  models: string[];
  result_count: number;
  result_files: string[];
};

type FormalizationRecord = {
  id: string;
  system: string;
  result: string;
  model_relation: string;
  status: string;
  source: string;
  declarations: string[];
  coordinates: string | null;
  lattice_kind: string | null;
  cell_count: number;
  degree_coordinates: string | null;
  degree_cell_count: number;
  note: string | null;
};

type FormalizationInventory = {
  reviewed_on: string | null;
  source: string;
  records: FormalizationRecord[];
  lattice: { cell_count: number };
  degree_lattice: { cell_count: number };
};

type LeaderboardPayload = {
  accepted_eligible_results: number;
  current_result_count: number;
  entries: Leader[];
  accepted_problems: AcceptedProblem[];
  formalization_inventory: FormalizationInventory;
};

const repo = "https://github.com/Vilin97/homotopy-groups-lean";
const liveLeaderboardUrl =
  `${repo.replace("github.com", "raw.githubusercontent.com")}/main/website/public/data/leaderboard.json`;
const initialData = initialLeaderboard as unknown as LeaderboardPayload;

const subscripts: Record<string, string> = {
  "0": "₀", "1": "₁", "2": "₂", "3": "₃", "4": "₄", "5": "₅",
  "6": "₆", "7": "₇", "8": "₈", "9": "₉", "k": "ₖ", "n": "ₙ", "+": "₊",
};
const superscripts: Record<string, string> = {
  "0": "⁰", "1": "¹", "2": "²", "3": "³", "4": "⁴", "5": "⁵",
  "6": "⁶", "7": "⁷", "8": "⁸", "9": "⁹", "n": "ⁿ", "k": "ᵏ", "+": "⁺",
};

function script(value: string, glyphs: Record<string, string>): string {
  return [...value].map((character) => glyphs[character] ?? character).join("");
}

function prettifyMath(value: string): string {
  return value
    .replace(/pi_([0-9kn+]+)\(S\^([0-9kn+]+)\)/g, (_, degree: string, sphere: string) =>
      `π${script(degree, subscripts)}(S${script(sphere, superscripts)})`)
    .replace(/pi_([0-9kn+]+)\(Circle\)/g, (_, degree: string) =>
      `π${script(degree, subscripts)}(Circle)`)
    .replace(/\bZ\b/g, "ℤ")
    .replace(/k<n/g, "k < n");
}

function statusLabel(status: string): string {
  if (status === "dual_kernel_verified_reference") return "dual-kernel verified";
  if (status === "source_audited_imported_submission") return "imported · source audited";
  if (status === "source_audited_historical") return "historical · source audited";
  if (status === "source_audited_builds") return "builds · source audited";
  return status.replaceAll("_", " ");
}

export function Leaderboard() {
  const [data, setData] = useState<LeaderboardPayload>(initialData);

  useEffect(() => {
    fetch(`${liveLeaderboardUrl}?v=${Date.now()}`, { cache: "no-store" })
      .then((response) => response.ok ? response.json() : Promise.reject(new Error("leaderboard fetch failed")))
      .then((payload: Partial<LeaderboardPayload>) => {
        if (!Array.isArray(payload.entries)) return;
        setData((current) => ({
          ...current,
          ...payload,
          entries: payload.entries ?? current.entries,
          accepted_problems: Array.isArray(payload.accepted_problems)
            ? payload.accepted_problems
            : current.accepted_problems,
          formalization_inventory: payload.formalization_inventory?.lattice
            ? payload.formalization_inventory
            : current.formalization_inventory,
        }));
      })
      .catch(() => undefined);
  }, []);

  const acceptedById = useMemo(
    () => new Map(data.accepted_problems.map((problem) => [problem.id, problem])),
    [data.accepted_problems],
  );
  const firstCount = data.entries.reduce((total, entry) => total + entry.firsts, 0);

  return (
    <div className="leaderboard-stack">
      <div className="eval-stats" aria-label="Verified-result summary">
        <div><strong>{data.accepted_eligible_results}</strong><span>scored solves</span></div>
        <div><strong>{firstCount}</strong><span>first solves</span></div>
        <div><strong>{data.current_result_count}</strong><span>current records</span></div>
        <div><strong>{data.formalization_inventory.degree_lattice.cell_count}</strong><span>formalized degree cells</span></div>
      </div>

      <section className="leaderboard-card" aria-labelledby="ranked-results-title">
        <div className="leader-panel-head">
          <div><span>RANKED CONTRIBUTORS</span><h3 id="ranked-results-title">Verified evaluator results</h3></div>
          <p>Expand a row to see the named challenges behind its score.</p>
        </div>
        {data.entries.length === 0 ? (
          <div className="empty-state">
            <div className="empty-orbit">π</div>
            <div><strong>The first place is open.</strong><p>No external submission has passed the public evaluator yet.</p></div>
            <a className="button primary" href={`${repo}/issues/new?template=submit.yml`}>Claim a theorem <span aria-hidden="true">↗</span></a>
          </div>
        ) : (
          <div className="leader-entries">
            {data.entries.map((entry) => (
              <details className="leader-entry" key={entry.actor}>
                <summary>
                  <span className="leader-rank">{String(entry.rank).padStart(2, "0")}</span>
                  <span className="leader-identity"><strong>@{entry.actor}</strong><small>{entry.models.join(" · ")}</small></span>
                  <span className="leader-score"><strong>{entry.solved}</strong><small>solved</small></span>
                  <span className="leader-score"><strong>{entry.firsts}</strong><small>firsts</small></span>
                  <i aria-hidden="true">⌄</i>
                </summary>
                <div className="leader-entry-body">
                  <div>
                    <span className="leader-section-label">PROBLEMS SOLVED</span>
                    <div className="solved-problem-grid">
                      {entry.problems.map((problemId) => {
                        const problem = acceptedById.get(problemId);
                        return (
                          <a href={`${repo}/blob/main/manifests/problems/${problemId}.toml`} key={problemId}>
                            <strong>{problem?.title ?? problemId}</strong>
                            <small>{problemId}</small>
                            {problem?.first_actor === entry.actor && <span>first solve</span>}
                          </a>
                        );
                      })}
                    </div>
                  </div>
                  <aside>
                    <span className="leader-section-label">PROVENANCE</span>
                    <dl>
                      <div><dt>Contributor</dt><dd>@{entry.actor}</dd></div>
                      <div><dt>Models</dt><dd>{entry.models.join(", ")}</dd></div>
                      <div><dt>Scoring</dt><dd>distinct accepted challenges</dd></div>
                    </dl>
                  </aside>
                </div>
              </details>
            ))}
          </div>
        )}
      </section>

      {data.accepted_problems.length > 0 && (
        <section className="coverage-panel" aria-labelledby="coverage-matrix-title">
          <div className="leader-panel-head">
            <div><span>PROBLEM-FIRST VIEW</span><h3 id="coverage-matrix-title">Accepted-result coverage</h3></div>
            <p>Every row is generated from an immutable evaluator record.</p>
          </div>
          <div className="coverage-table-wrap">
            <table className="coverage-table">
              <thead><tr><th scope="col">Problem</th>{data.entries.map((entry) => <th scope="col" key={entry.actor}>@{entry.actor}</th>)}<th scope="col">Record</th></tr></thead>
              <tbody>
                {data.accepted_problems.map((problem) => (
                  <tr key={problem.id}>
                    <th scope="row"><a href={`${repo}/blob/main/manifests/problems/${problem.id}.toml`}>{problem.title}</a><small>{problem.id} · {problem.family}</small></th>
                    {data.entries.map((entry) => (
                      <td aria-label={`${entry.actor} ${problem.actors.includes(entry.actor) ? "has" : "has not"} solved ${problem.title}`} className={problem.actors.includes(entry.actor) ? "solved" : "unsolved"} key={entry.actor}>{problem.actors.includes(entry.actor) ? "✓" : "—"}</td>
                    ))}
                    <td><a href={`${repo}/blob/main/results/${problem.result_files[0]}`}>{problem.score_eligible ? "scored" : "reference"} ↗</a></td>
                  </tr>
                ))}
              </tbody>
            </table>
          </div>
        </section>
      )}

      <section className="formalization-panel" aria-labelledby="formalization-index-title">
        <div className="leader-panel-head">
          <div><span>FORMALIZATION COVERAGE</span><h3 id="formalization-index-title">Which homotopy groups are in Lean?</h3></div>
          <p>Audited proofs are shown separately from competitive score.</p>
        </div>
        <div className="formalization-grid">
          {data.formalization_inventory.records.map((record) => (
            <article key={record.id}>
              <div className="formalization-meta"><span>{record.system}</span><strong>{statusLabel(record.status)}</strong></div>
              <h4>{prettifyMath(record.result)}</h4>
              <p>{record.model_relation}</p>
              <div className="formalization-foot">
                <span>{record.degree_coordinates
                  ? `${record.degree_cell_count.toLocaleString()} degree cells · ${record.degree_coordinates}`
                  : record.coordinates
                    ? `${record.cell_count} stem cells · ${record.coordinates}`
                    : "outside the displayed lattice"}</span>
                <a href={record.source}>Lean proof ↗</a>
              </div>
            </article>
          ))}
        </div>
        <a className="inventory-link" href={data.formalization_inventory.source}>machine-readable audit · reviewed {data.formalization_inventory.reviewed_on} ↗</a>
      </section>
    </div>
  );
}
