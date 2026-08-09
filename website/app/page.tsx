import openProblemData from "../public/data/open-problems.json";
import stableStemData from "../public/data/stable-stems.json";
import trackerData from "../public/data/tracker.json";
import { Frontiers } from "./frontiers";
import { Lattice } from "./lattice";
import { Leaderboard } from "./leaderboard";
import { siteAsset } from "./site";
import { Tracker } from "./tracker";

const repo = "https://github.com/Vilin97/homotopy-groups-lean";
const exactStemCount = stableStemData.stems.filter((stem) => stem.is_exact).length;
const partialStemCount = stableStemData.stems.length - exactStemCount;

const reportPdf = siteAsset(
  "/reports/homotopy-groups-of-spheres-literature-review.pdf",
);
const comprehensiveReport = siteAsset("/reports/comprehensive-2026/");

// The public site has no request-specific state; make that invariant explicit
// so static-only hosts receive a concrete index.html.
export const dynamic = "force-static";

export default function Home() {
  return (
    <main>
      <nav className="site-nav shell" aria-label="Primary navigation">
        <a className="wordmark" href="#top" aria-label="Homotopy Groups Lean home">
          <span aria-hidden="true">π</span>
          <strong>HGL</strong>
        </a>
        <div className="site-nav-links">
          <a href="#frontiers">Frontiers</a>
          <a href="#atlas">Atlas</a>
          <a href="#problems">Problems</a>
          <a href="#leaderboard">Leaderboard</a>
          <a href={comprehensiveReport}>Report</a>
          <a href={`${repo}#hosted-submission-flow`}>Submit ↗</a>
        </div>
        <a className="repo-link" href={repo}>GitHub <span aria-hidden="true">↗</span></a>
      </nav>

      <header className="atlas-hero shell" id="top">
        <div className="hero-title">
          <p>
            <span>{trackerData.problem_count} Lean challenges</span>
            <span>integral atlas 0–90</span>
            <span>3-local / primary through 108</span>
            <span>structured ledgers to 1000</span>
          </p>
          <h1><span className="math-expression">π<sub>n+k</sub>(S<sup>n</sup>)</span>, <em>mapped.</em></h1>
        </div>
        <div className="hero-notation" aria-label="Stable range formula">
          <span>k ≤ n − 2</span>
          <i>⇒</i>
          <strong className="stable-formula">
            <span className="math-expression">π<sub>n+k</sub>(S<sup>n</sup>)</span>
            <span aria-hidden="true">≅</span>
            <span className="math-expression">π<sub>k</sub>(𝕊)</span>
          </strong>
        </div>
        <div className="hero-bottom">
          <p>Separate complete groups, primary components, named classes, and periodic families.</p>
          <a href="#frontiers">enter the stable frontiers ↓</a>
        </div>
      </header>

      <section className="frontier-section shell" id="frontiers" aria-labelledby="frontiers-title">
        <div className="compact-heading">
          <div>
            <span>BEYOND STEM 90</span>
            <h2 id="frontiers-title">Stable frontier atlas</h2>
          </div>
          <div className="heading-math">
            <span>3-local degree 0 · p-primary exact 1–108</span>
            <span>5-primary ledger 0–999</span>
            <strong>image J / v₁ in all stems</strong>
            <a href={comprehensiveReport}>2026 report ↗</a>
          </div>
        </div>
        <Frontiers />
      </section>

      <section className="atlas-section shell" id="atlas" aria-labelledby="atlas-title">
        <div className="compact-heading">
          <div>
            <span>THE (n,k)-PLANE</span>
            <h2 id="atlas-title">Knowledge lattice</h2>
          </div>
          <div className="heading-math">
            <span>n = 1…92</span>
            <span>k = 0…90</span>
            <strong>{exactStemCount} exact stems · {partialStemCount} partial</strong>
            <a href={reportPdf}>earlier low-stem PDF ↗</a>
          </div>
        </div>
        <Lattice />
      </section>

      <section className="workbench shell" id="problems" aria-labelledby="problems-title">
        <div className="compact-heading">
          <div>
            <span>LEAN CORPUS</span>
            <h2 id="problems-title">Proof queue</h2>
          </div>
          <div className="heading-math">
            <span>{trackerData.problem_count} declarations</span>
            <a href={`${repo}/blob/main/research/open-problems.md`}>
              {openProblemData.conjectures.length} conjecture families ↗
            </a>
            <a href={`${repo}/tree/main/manifests/problems`}>all manifests ↗</a>
          </div>
        </div>
        <Tracker />
      </section>

      <section className="leaderboard-section shell" id="leaderboard" aria-labelledby="leaderboard-title">
        <div className="compact-heading">
          <div>
            <span>VERIFIED OUTPUT</span>
            <h2 id="leaderboard-title">Leaderboard</h2>
          </div>
          <div className="heading-math">
            <span>distinct solved problems</span>
            <span>reference proofs score 0</span>
          </div>
        </div>
        <Leaderboard />
      </section>

      <section className="proof-gate shell" aria-label="Proof verification pipeline">
        <div><span>01</span><strong>Submission.lean</strong></div>
        <i aria-hidden="true">→</i>
        <div><span>02</span><strong>Comparator</strong></div>
        <i aria-hidden="true">→</i>
        <div><span>03a</span><strong>Lean kernel</strong></div>
        <b aria-hidden="true">+</b>
        <div><span>03b</span><strong>nanoda</strong></div>
        <i aria-hidden="true">→</i>
        <div className="gate-accepted"><span>✓</span><strong>accepted</strong></div>
      </section>

      <footer>
        <div className="shell lean-footer">
          <a className="wordmark" href="#top"><span aria-hidden="true">π</span><strong>HGL</strong></a>
          <p><span className="math-expression">π<sub>n+k</sub>(S<sup>n</sup>)</span> · Lean 4.32.2 · Apache-2.0</p>
          <div>
            <a href={comprehensiveReport}>2026 report</a>
            <a href={reportPdf}>earlier PDF</a>
            <a href={`${repo}/blob/main/SECURITY.md`}>trust model</a>
            <a href={`${repo}/tree/main/research`}>sources</a>
            <a href={repo}>code ↗</a>
          </div>
        </div>
      </footer>
    </main>
  );
}
