import openProblemData from "../public/data/open-problems.json";
import stableStemData from "../public/data/stable-stems.json";
import trackerData from "../public/data/tracker.json";
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
          <a href="#atlas">Atlas</a>
          <a href="#problems">Problems</a>
          <a href="#leaderboard">Leaderboard</a>
          <a href={reportPdf}>Report</a>
          <a href={`${repo}#hosted-submission-flow`}>Submit ↗</a>
        </div>
        <a className="repo-link" href={repo}>GitHub <span aria-hidden="true">↗</span></a>
      </nav>

      <header className="atlas-hero shell" id="top">
        <div className="hero-title">
          <p>
            <span>{trackerData.problem_count} Lean challenges</span>
            <span>stems 0–90</span>
            <span>dual-kernel checked</span>
          </p>
          <h1>π<sub>n+k</sub>(S<sup>n</sup>), <em>mapped.</em></h1>
        </div>
        <div className="hero-notation" aria-label="Stable range formula">
          <span>k ≤ n − 2</span>
          <i>⇒</i>
          <strong>π<sub>n+k</sub>(S<sup>n</sup>) ≅ π<sub>k</sub><sup>S</sup></strong>
        </div>
        <div className="hero-bottom">
          <p>Click a coordinate. See the group, the evidence, and the gaps.</p>
          <a href="#atlas">enter the (n,k)-plane ↓</a>
        </div>
      </header>

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
            <a href={reportPdf}>literature review ↗</a>
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
          <p>π<sub>n+k</sub>(S<sup>n</sup>) · Lean 4.32.2 · Apache-2.0</p>
          <div>
            <a href={reportPdf}>report</a>
            <a href={`${repo}/blob/main/SECURITY.md`}>trust model</a>
            <a href={`${repo}/tree/main/research`}>sources</a>
            <a href={repo}>code ↗</a>
          </div>
        </div>
      </footer>
    </main>
  );
}
