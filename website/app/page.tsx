import Link from "next/link";
import openProblemData from "../public/data/open-problems.json";
import stableStemData from "../public/data/stable-stems.json";
import trackerData from "../public/data/tracker.json";
import { Leaderboard } from "./leaderboard";
import { Tracker } from "./tracker";

const repo = "https://github.com/Vilin97/homotopy-groups-lean";

const stems = stableStemData.stems.map((row) => ({
  stem: row.stem,
  status: row.is_exact ? "exact" : "open",
}));

const openProblems = openProblemData.conjectures;
const exactStemCount = stems.filter((row) => row.status === "exact").length;
const ambiguousStemCount = stems.length - exactStemCount;
const leanReadyConjectureCount = openProblems.filter(
  (problem) => problem.lean.status === "statement_available",
).length;

const steps = [
  {
    index: "01",
    title: "Choose a theorem",
    copy: "Every challenge has a stable identifier, a typed Lean statement, provenance, and an explicit knowledge status.",
  },
  {
    index: "02",
    title: "Submit only proof code",
    copy: "The evaluator takes Submission.lean from a public commit. Toolchains, statements, and trust policy stay pristine.",
  },
  {
    index: "03",
    title: "Pass both kernels",
    copy: "Comparator checks the exported declaration graph, then Lean's kernel and the independent nanoda kernel replay it.",
  },
];

export default function Home() {
  return (
    <main>
      <nav className="nav shell" aria-label="Primary navigation">
        <Link className="brand" href="#top" aria-label="Homotopy Groups Lean home">
          <span className="brand-mark" aria-hidden="true">π</span>
          <span>Homotopy Groups <i>/ Lean</i></span>
        </Link>
        <div className="nav-links">
          <Link href="#tracker">Tracker</Link>
          <Link href="#leaderboard">Leaderboard</Link>
          <a href={`${repo}#hosted-submission-flow`}>Submit</a>
          <a className="github-link" href={repo}>GitHub <span aria-hidden="true">↗</span></a>
        </div>
      </nav>

      <section className="hero shell" id="top">
        <div className="hero-copy">
          <p className="eyebrow"><span /> An open formalization benchmark</p>
          <h1>The known edge of<br />homotopy, <em>formalized.</em></h1>
          <p className="lede">
            A versioned Lean benchmark for the homotopy groups of spheres and spaces—from
            foundational theorems to unresolved stable stems. Every accepted proof is checked
            against a pristine statement by two kernels.
          </p>
          <div className="hero-actions">
            <a className="button primary" href="#tracker">Explore the tracker <span aria-hidden="true">↓</span></a>
            <a className="button secondary" href={repo}>Read the benchmark <span aria-hidden="true">↗</span></a>
          </div>
        </div>
        <div className="orbit-panel" aria-label="Abstract visualization of sphere maps">
          <div className="coordinate-grid" />
          <div className="orbit orbit-one"><span /></div>
          <div className="orbit orbit-two"><span /></div>
          <div className="sphere sphere-a">S<sup>n+k</sup></div>
          <div className="sphere sphere-b">S<sup>n</sup></div>
          <div className="map-arrow"><span>f</span></div>
          <div className="formula">π<sub>n+k</sub>(S<sup>n</sup>)</div>
          <div className="panel-note">MAPS · CLASSES · PROOFS</div>
        </div>
      </section>

      <section className="stat-band" aria-label="Benchmark statistics">
        <div className="shell stats">
          <div><strong>{trackerData.problem_count}</strong><span>Lean statements tracked</span></div>
          <div><strong>{exactStemCount}</strong><span>exact in stems 0–90</span></div>
          <div><strong>{String(ambiguousStemCount).padStart(2, "0")}</strong><span>published ambiguities</span></div>
          <div><strong>{String(openProblems.length).padStart(2, "0")}</strong><span>conjecture families</span></div>
        </div>
      </section>

      <section className="coverage shell" aria-labelledby="coverage-title">
        <div className="section-heading">
          <div>
            <p className="eyebrow"><span /> Knowledge map</p>
            <h2 id="coverage-title">Stable stems, 0 through 90</h2>
          </div>
          <p>
            The 2023 Isaksen–Wang–Xu table, with peer-reviewed 2025 corrections.
            Ambiguous additive extensions remain visible—not silently guessed.
          </p>
        </div>
        <div className="stem-map" role="img" aria-label="Stable stems zero through ninety; stems 84, 85, 86, and 90 have published alternatives, all others are exact">
          {stems.map(({ stem, status }) => (
            <span className={`stem ${status}`} key={stem} title={`Stem ${stem}: ${status === "exact" ? "exact value known" : "published alternatives"}`}>
              {stem}
            </span>
          ))}
        </div>
        <div className="legend">
          <span><i className="legend-dot exact" /> Exact published value</span>
          <span><i className="legend-dot open" /> Published additive alternatives</span>
          <a href={`${repo}/tree/main/research`}>View provenance <span aria-hidden="true">↗</span></a>
        </div>
      </section>

      <section className="tracker-section" id="tracker" aria-labelledby="tracker-title">
        <div className="shell">
          <div className="section-heading inverse">
            <div>
              <p className="eyebrow"><span /> Live corpus</p>
              <h2 id="tracker-title">The theorem tracker</h2>
            </div>
            <p>
              Computed mathematics and formalization progress are separate axes.
              Filter the launch corpus by what is proved, claimed, or still unknown.
            </p>
          </div>
          <Tracker />
          <div className="open-registry" aria-labelledby="open-registry-title">
            <div className="open-registry-heading">
              <div>
                <p className="eyebrow"><span /> Open mathematics</p>
                <h3 id="open-registry-title">Six conjecture families, honestly scoped</h3>
              </div>
              <p>{leanReadyConjectureCount} have comparator-ready Lean statements; {openProblems.length - leanReadyConjectureCount} are retained as foundation-blocked research targets.</p>
            </div>
            <div className="open-problem-grid">
              {openProblems.map((problem) => (
                <a href={problem.source.url} key={problem.id}>
                  <strong>{problem.title}</strong>
                  <span>{problem.lean.status === "statement_available" ? "Lean statement available" : "Blocked on missing foundations"} ↗</span>
                </a>
              ))}
            </div>
          </div>
        </div>
      </section>

      <section className="trust shell" aria-labelledby="trust-title">
        <div className="trust-copy">
          <p className="eyebrow"><span /> Trust boundary</p>
          <h2 id="trust-title">A proof earns its checkmark.</h2>
          <p>
            A green build alone is not a proof. The evaluator fixes the challenge, resolves every
            submission to an immutable commit, permits only the standard Lean axioms, and checks
            the resulting declaration graph independently.
          </p>
          <a href={`${repo}/blob/main/SECURITY.md`}>Read the evaluator threat model <span aria-hidden="true">↗</span></a>
        </div>
        <div className="pipeline" aria-label="Submission verification pipeline">
          <div className="pipeline-node"><span>01</span><strong>Pristine statement</strong><small>benchmark-owned</small></div>
          <i aria-hidden="true">→</i>
          <div className="pipeline-node"><span>02</span><strong>Comparator</strong><small>exact declaration graph</small></div>
          <i aria-hidden="true">→</i>
          <div className="pipeline-node"><span>03</span><strong>Two kernels</strong><small>Lean + nanoda</small></div>
          <i aria-hidden="true">→</i>
          <div className="pipeline-node accepted"><span>✓</span><strong>Accepted</strong><small>SHA-pinned result</small></div>
        </div>
      </section>

      <section className="submit-flow">
        <div className="shell">
          <div className="section-heading">
            <div>
              <p className="eyebrow"><span /> Submission flow</p>
              <h2>From theorem to verified artifact</h2>
            </div>
          </div>
          <div className="steps">
            {steps.map((step) => (
              <article key={step.index}>
                <span>{step.index}</span>
                <h3>{step.title}</h3>
                <p>{step.copy}</p>
              </article>
            ))}
          </div>
        </div>
      </section>

      <section className="leaderboard shell" id="leaderboard" aria-labelledby="leaderboard-title">
        <div className="section-heading">
          <div>
            <p className="eyebrow"><span /> Public record</p>
            <h2 id="leaderboard-title">Leaderboard</h2>
          </div>
          <p>Accepted external proofs will appear here, ordered by distinct challenges solved. Reference proofs never earn points.</p>
        </div>
        <Leaderboard />
      </section>

      <footer>
        <div className="shell footer-main">
          <div>
            <Link className="brand footer-brand" href="#top"><span className="brand-mark">π</span><span>Homotopy Groups <i>/ Lean</i></span></Link>
            <p>Formalizing the frontier, one exact statement at a time.</p>
          </div>
          <div className="footer-links">
            <div><strong>Benchmark</strong><a href={`${repo}/tree/main/manifests/problems`}>Problems</a><a href={`${repo}/tree/main/results`}>Results</a><a href={`${repo}/blob/main/CONTRIBUTING.md`}>Contribute</a></div>
            <div><strong>Research</strong><a href={`${repo}/tree/main/research`}>Sources</a><a href="https://www.numdam.org/articles/10.1007/s10240-023-00139-1/">IWX table ↗</a><a href="https://link.springer.com/article/10.1007/s42543-025-00098-y">2025 corrections ↗</a></div>
          </div>
        </div>
        <div className="shell footer-bottom"><span>Apache-2.0 · Open benchmark · Versioned claims</span><span>LEAN 4.32.2</span></div>
      </footer>
    </main>
  );
}
