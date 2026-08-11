"use client";

import {
  type FormEvent,
  type KeyboardEvent,
  type PointerEvent,
  useEffect,
  useMemo,
  useRef,
  useState,
} from "react";
import leaderboardData from "../public/data/leaderboard.json";
import stableStemData from "../public/data/stable-stems.json";
import { siteAsset } from "./site";

type Decomposition = { free_rank: number; torsion_invariant_factors: number[] };
type Group = { integral_decomposition: Decomposition };
type StableStem = {
  stem: number;
  is_exact: boolean;
  group?: Group;
  alternatives?: Array<{ alternative_id: string; group: Group }>;
  note?: string;
  source_refs: Array<{ source_id: string }>;
};
type Knowledge = "exact" | "partial" | "primary" | "disputed" | "uncharted";
type Formalization = {
  accessibleLabel: string;
  badge: string;
  kind: "lean4-exact" | "lean4" | "historical";
  note: string;
  source: string;
} | null;
type FormalizationRecord = {
  id: string;
  system: string;
  result: string;
  model_relation: string;
  status: string;
  source: string;
  lattice_kind: string | null;
};
type FormalizationCell = { n: number; k: number; record_id: string };
type FormalizationInventory = {
  source: string;
  records: FormalizationRecord[];
  lattice: { cells: FormalizationCell[] };
};
type Coordinate = { n: number; k: number };
type CanvasGeometry = { left: number; top: number; cell: number };

const stems = stableStemData.stems as StableStem[];
const sources = new Map(stableStemData.sources.map((source) => [source.source_id, source.url]));
const nMin = 1;
const nMax = 92;
const kMax = 90;
const rowCount = nMax - nMin + 1;
const columnCount = kMax + 1;
const formalizationInventory = leaderboardData.formalization_inventory as FormalizationInventory;
const formalizationRecords = new Map(
  formalizationInventory.records.map((record) => [record.id, record]),
);
const formalizationCells = new Map(
  formalizationInventory.lattice.cells.map((cell) => [`${cell.n}:${cell.k}`, cell.record_id]),
);

const knowledgeCopy: Record<Knowledge, { label: string; short: string; color: string }> = {
  exact: { label: "Exact integral", short: "exact integral group", color: "#4fdda8" },
  partial: { label: "Alternatives", short: "published integral alternatives", color: "#ffb75e" },
  primary: { label: "2-primary", short: "exact 2-primary component only", color: "#5da9d6" },
  disputed: { label: "Disputed", short: "conflicting published computations", color: "#e36d86" },
  uncharted: { label: "Not tabulated", short: "not fully tabulated in the review", color: "#303947" },
};

function isStable(n: number, k: number): boolean {
  return k <= n - 2;
}

function knowledgeAt(n: number, k: number): Knowledge {
  // S¹ is K(Z,1): the first group is Z and every higher group vanishes.
  if (n === 1) return "exact";
  // Toda's tables cover stems 0–19 and Mimura–Toda completes stem 20.
  if (k <= 20) return "exact";
  if (isStable(n, k)) return stems[k]?.is_exact ? "exact" : "partial";
  // Published 2-primary unstable computations in the review.
  if (k >= 21 && k <= 32) return "primary";
  if (k === 33 && ((n >= 2 && n <= 9) || (n >= 28 && n <= 34))) return "primary";
  if (k === 33 && n === 27) return "disputed";
  return "uncharted";
}

function formalizationAt(n: number, k: number): Formalization {
  const recordId = formalizationCells.get(`${n}:${k}`);
  const record = recordId ? formalizationRecords.get(recordId) : undefined;
  if (!record) return null;
  const dualKernel = record.status === "dual_kernel_verified_reference";
  const kernelChecked = record.status === "lean_kernel_checked_local_source";
  const historical = record.status === "source_audited_historical";
  const exactMetricModel = record.lattice_kind === "lean4_exact_metric_model";
  const statusLabel = kernelChecked
    ? "kernel checked · exact metric model"
    : dualKernel
      ? "dual-kernel verified"
      : historical
        ? "historical · source audited"
        : "source audited";
  return {
    accessibleLabel: `${statusLabel} in ${record.system}`,
    badge: `${record.system} · ${statusLabel}`,
    kind: exactMetricModel
      ? "lean4-exact"
      : record.system.startsWith("Lean 4")
        ? "lean4"
        : "historical",
    note: `${record.result}. ${record.model_relation}.`,
    source: record.source,
  };
}

function superscript(value: number): string {
  const glyphs: Record<string, string> = {
    "0": "⁰", "1": "¹", "2": "²", "3": "³", "4": "⁴",
    "5": "⁵", "6": "⁶", "7": "⁷", "8": "⁸", "9": "⁹",
  };
  return String(value).split("").map((digit) => glyphs[digit]).join("");
}

function formatGroup(group?: Group): string {
  if (!group) return "—";
  const { free_rank: rank, torsion_invariant_factors: factors } = group.integral_decomposition;
  const pieces: string[] = [];
  if (rank === 1) pieces.push("ℤ");
  if (rank > 1) pieces.push(`ℤ${superscript(rank)}`);
  const counts = new Map<number, number>();
  for (const factor of factors) counts.set(factor, (counts.get(factor) ?? 0) + 1);
  for (const [factor, count] of counts) {
    pieces.push(count === 1 ? `ℤ/${factor}` : `(ℤ/${factor})${superscript(count)}`);
  }
  return pieces.join(" ⊕ ") || "0";
}

export function Lattice() {
  const [selected, setSelected] = useState<Coordinate>({ n: 1, k: 0 });
  const [jumpN, setJumpN] = useState("1");
  const [jumpK, setJumpK] = useState("0");
  const [canvasWidth, setCanvasWidth] = useState(720);
  const [shown, setShown] = useState<Record<Knowledge, boolean>>({
    exact: true, partial: true, primary: true, disputed: true, uncharted: true,
  });
  const [showFormalizations, setShowFormalizations] = useState(true);
  const canvasRef = useRef<HTMLCanvasElement>(null);
  const canvasFrameRef = useRef<HTMLDivElement>(null);
  const geometryRef = useRef<CanvasGeometry>({ left: 34, top: 25, cell: 7 });

  const counts = useMemo(() => {
    const knowledge: Record<Knowledge, number> = {
      exact: 0, partial: 0, primary: 0, disputed: 0, uncharted: 0,
    };
    let formalized = 0;
    for (let n = nMin; n <= nMax; n += 1) {
      for (let k = 0; k <= kMax; k += 1) {
        knowledge[knowledgeAt(n, k)] += 1;
        if (formalizationAt(n, k)) formalized += 1;
      }
    }
    return { knowledge, formalized };
  }, []);

  useEffect(() => {
    const frame = canvasFrameRef.current;
    if (!frame) return;
    const observer = new ResizeObserver(([entry]) =>
      setCanvasWidth(Math.max(280, Math.floor(entry.contentRect.width))));
    observer.observe(frame);
    setCanvasWidth(Math.max(280, Math.floor(frame.getBoundingClientRect().width)));
    return () => observer.disconnect();
  }, []);

  useEffect(() => {
    const canvas = canvasRef.current;
    if (!canvas) return;
    const context = canvas.getContext("2d");
    if (!context) return;
    const ratio = window.devicePixelRatio || 1;
    const left = 34;
    const top = 25;
    const right = 8;
    const bottom = 26;
    const cell = (canvasWidth - left - right) / columnCount;
    const height = top + cell * rowCount + bottom;
    geometryRef.current = { left, top, cell };
    canvas.width = Math.round(canvasWidth * ratio);
    canvas.height = Math.round(height * ratio);
    canvas.style.width = `${canvasWidth}px`;
    canvas.style.height = `${height}px`;
    context.setTransform(ratio, 0, 0, ratio, 0, 0);
    context.clearRect(0, 0, canvasWidth, height);
    context.fillStyle = "#080b10";
    context.fillRect(0, 0, canvasWidth, height);
    const gap = Math.max(.35, Math.min(1.1, cell * .12));
    for (let row = 0; row < rowCount; row += 1) {
      const n = nMin + row;
      for (let k = 0; k <= kMax; k += 1) {
        const status = knowledgeAt(n, k);
        const formalization = formalizationAt(n, k);
        const x = left + k * cell + gap / 2;
        const y = top + row * cell + gap / 2;
        context.globalAlpha = shown[status] ? .97 : .08;
        context.fillStyle = knowledgeCopy[status].color;
        context.fillRect(x, y, cell - gap, cell - gap);
        if (formalization && showFormalizations) {
          context.globalAlpha = 1;
          const inset = Math.max(.65, cell * .13);
          const outlineX = x + inset;
          const outlineY = y + inset;
          const outlineSize = Math.max(1, cell - gap - 2 * inset);
          // A dark keyline keeps the purple overlay visible on light evidence cells;
          // purple itself remains visible on the dark exact-integral cells.
          context.strokeStyle = "#080b10";
          context.lineWidth = Math.max(1.6, cell * .28);
          context.strokeRect(outlineX, outlineY, outlineSize, outlineSize);
          context.strokeStyle = formalization.kind === "lean4-exact"
            ? "#f0bfff"
            : formalization.kind === "lean4" ? "#aa8cff" : "#c4afff";
          context.lineWidth = Math.max(.8, cell * .12);
          context.strokeRect(outlineX, outlineY, outlineSize, outlineSize);
        }
      }
    }
    context.globalAlpha = 1;
    const selectedX = left + selected.k * cell + .5;
    const selectedY = top + (selected.n - nMin) * cell + .5;
    const selectedSize = Math.max(1, cell - 1);
    context.strokeStyle = "#f3f0e8";
    context.lineWidth = Math.max(2.4, cell * .34);
    context.strokeRect(selectedX, selectedY, selectedSize, selectedSize);
    context.strokeStyle = "#4fdda8";
    context.lineWidth = Math.max(1.1, cell * .15);
    context.strokeRect(selectedX, selectedY, selectedSize, selectedSize);
    context.fillStyle = "#7c899b";
    context.font = "8px ui-monospace, SFMono-Regular, Menlo, monospace";
    context.textAlign = "center";
    for (let k = 0; k <= kMax; k += 10) context.fillText(String(k), left + (k + .5) * cell, 15);
    context.textAlign = "right";
    for (let n = 10; n <= nMax; n += 10) context.fillText(String(n), left - 6, top + (n - nMin + .8) * cell);
    context.fillStyle = "#4fdda8";
    context.font = "italic 11px Georgia, serif";
    context.textAlign = "left";
    context.fillText("n", 10, 14);
    context.textAlign = "right";
    context.fillText("k →", canvasWidth - 8, height - 8);
  }, [canvasWidth, selected, shown, showFormalizations]);

  const selectCoordinate = (coordinate: Coordinate) => {
    setSelected(coordinate);
    setJumpN(String(coordinate.n));
    setJumpK(String(coordinate.k));
  };
  const locate = (event: FormEvent) => {
    event.preventDefault();
    const n = Math.min(nMax, Math.max(nMin, Number.parseInt(jumpN, 10) || nMin));
    const k = Math.min(kMax, Math.max(0, Number.parseInt(jumpK, 10) || 0));
    selectCoordinate({ n, k });
    canvasRef.current?.focus();
  };
  const coordinateFromPointer = (event: PointerEvent<HTMLCanvasElement>): Coordinate | null => {
    const bounds = event.currentTarget.getBoundingClientRect();
    const scaleX = canvasWidth / bounds.width;
    const scaleY = Number.parseFloat(event.currentTarget.style.height) / bounds.height;
    const { left, top, cell } = geometryRef.current;
    const k = Math.floor(((event.clientX - bounds.left) * scaleX - left) / cell);
    const row = Math.floor(((event.clientY - bounds.top) * scaleY - top) / cell);
    if (k < 0 || k > kMax || row < 0 || row >= rowCount) return null;
    return { n: nMin + row, k };
  };
  const inspectPointer = (event: PointerEvent<HTMLCanvasElement>) => {
    const coordinate = coordinateFromPointer(event);
    if (coordinate && (coordinate.n !== selected.n || coordinate.k !== selected.k)) selectCoordinate(coordinate);
  };
  const moveWithKeys = (event: KeyboardEvent<HTMLCanvasElement>) => {
    const movement: Record<string, Coordinate> = {
      ArrowUp: { n: Math.max(nMin, selected.n - 1), k: selected.k },
      ArrowDown: { n: Math.min(nMax, selected.n + 1), k: selected.k },
      ArrowLeft: { n: selected.n, k: Math.max(0, selected.k - 1) },
      ArrowRight: { n: selected.n, k: Math.min(kMax, selected.k + 1) },
    };
    if (!movement[event.key]) return;
    event.preventDefault();
    selectCoordinate(movement[event.key]);
  };

  const status = knowledgeAt(selected.n, selected.k);
  const formalization = formalizationAt(selected.n, selected.k);
  const stem = stems[selected.k];
  const stable = isStable(selected.n, selected.k);
  const sourceUrl = stable
    ? stem?.source_refs.map((ref) => sources.get(ref.source_id)).find(Boolean)
    : siteAsset("/reports/homotopy-groups-of-spheres-literature-review.pdf");
  const obviousGroup = selected.n === 1
    ? (selected.k === 0 ? "ℤ" : "0")
    : selected.k === 0 || (selected.n === 2 && selected.k === 1)
      ? "ℤ"
      : stable && status === "exact"
        ? formatGroup(stem.group)
        : null;

  return (
    <div className="atlas-card">
      <div className="atlas-toolbar">
        <div className="knowledge-legend" aria-label="Toggle lattice evidence classes" role="group">
          {(Object.keys(knowledgeCopy) as Knowledge[]).map((key) => (
            <button aria-pressed={shown[key]} className={`legend-control ${key}`} key={key}
              onClick={() => setShown((current) => ({ ...current, [key]: !current[key] }))} type="button">
              <i aria-hidden="true" style={{ background: knowledgeCopy[key].color }} />
              <span>{knowledgeCopy[key].label}</span><strong>{counts.knowledge[key].toLocaleString()}</strong>
            </button>
          ))}
          <button aria-pressed={showFormalizations} className="legend-control formalized"
            onClick={() => setShowFormalizations((current) => !current)} type="button">
            <i aria-hidden="true" /><span>Lean overlay</span><strong>{counts.formalized}</strong>
          </button>
        </div>
        <form className="coordinate-jump" onSubmit={locate}>
          <label><span>n</span><input aria-label="Sphere dimension n" max={nMax} min={nMin} onChange={(event) => setJumpN(event.target.value)} type="number" value={jumpN} /></label>
          <label><span>k</span><input aria-label="Stem k" max={kMax} min="0" onChange={(event) => setJumpK(event.target.value)} type="number" value={jumpK} /></label>
          <button type="submit">Locate</button>
        </form>
      </div>
      <div className="atlas-main">
        <div className="lattice-wrap">
          <div className="lattice-axis-title"><span className="math-expression">π<sub>n+k</sub>(S<sup>n</sup>)</span><strong>hover · click · arrow keys</strong></div>
          <p className="sr-only" id="lattice-instructions">Use the arrow keys to inspect adjacent cells, or enter n and k in the locate form.</p>
          <div className="canvas-frame" ref={canvasFrameRef}>
            <canvas
              aria-describedby="lattice-instructions"
              aria-label={`Interactive evidence lattice. Selected pi_${selected.n + selected.k}(S^${selected.n}): ${knowledgeCopy[status].short}${formalization ? `, ${formalization.accessibleLabel}` : ""}.`}
              className="lattice-canvas" onClick={inspectPointer} onKeyDown={moveWithKeys}
              onPointerMove={inspectPointer} ref={canvasRef} tabIndex={0}
            >Use the coordinate form to inspect the evidence lattice.</canvas>
          </div>
          <div className="k-axis"><span>n = 1…92</span><strong>k = m − n = 0…90</strong></div>
        </div>
        <aside className={`coordinate-detail ${status}`} aria-live="polite">
          <div className="detail-status"><i aria-hidden="true" style={{ background: knowledgeCopy[status].color }} /> {knowledgeCopy[status].label}</div>
          {formalization && <div className="formalization-badge">{formalization.badge}</div>}
          <h3 className="math-expression">π<sub>{selected.n + selected.k}</sub>(S<sup>{selected.n}</sup>)</h3>
          <div className="coordinate-pair"><span>n = {selected.n}</span><span>k = {selected.k}</span></div>
          {obviousGroup && <div className="group-value"><span>integral group</span><strong>{obviousGroup}</strong></div>}
          {status === "exact" && !obviousGroup && stable && <div className="group-value"><span className="math-expression">≅ π<sub>{selected.k}</sub>(𝕊)</span><strong>{formatGroup(stem.group)}</strong></div>}
          {status === "exact" && !obviousGroup && !stable && <p>The complete integral group is tabulated in Toda&apos;s 0–19 stem tables or the Mimura–Toda 20-stem computation reproduced in the review.</p>}
          {status === "partial" && <><div className="group-value"><span>published full groups</span><strong>{stem.alternatives?.length ?? 0} alternatives</strong></div><div className="alternatives">{stem.alternatives?.map((alternative, index) => <span key={alternative.alternative_id}><b>{String.fromCharCode(65 + index)}</b>{formatGroup(alternative.group)}</span>)}</div><p>{stem.note}</p></>}
          {status === "primary" && <><div className="group-value"><span>computed component</span><strong>2-primary</strong></div><p>The 2-primary component is tabulated, but this view does not claim a complete integral group.</p></>}
          {status === "disputed" && <><div className="group-value"><span>33-stem</span><strong>conflicting values</strong></div><p>The literature review records incompatible published values at n = 27. This cell stays visibly disputed.</p></>}
          {status === "uncharted" && <><div className="group-value"><span>review coverage</span><strong>not fully tabulated</strong></div><p>Gray means the attached review does not provide a complete integral value here—not that mathematics knows nothing about the group.</p></>}
          {formalization && <p className="formalization-note">{formalization.note} It does not change the literature evidence class beneath it.</p>}
          <div className="detail-links">
            {formalization && <a href={formalization.source}>Lean source ↗</a>}
            {formalization && <a href={formalizationInventory.source}>full inventory ↗</a>}
            {sourceUrl && <a href={sourceUrl}>mathematical source ↗</a>}
          </div>
        </aside>
      </div>
      <p className="atlas-scope">Audited 92 × 91 view: <b>{counts.knowledge.exact.toLocaleString()} exact integral</b>, <b>{counts.knowledge.partial.toLocaleString()} published-alternative</b>, <b>{counts.knowledge.primary.toLocaleString()} exact 2-primary-only</b>, <b>{counts.knowledge.disputed.toLocaleString()} disputed</b>, and <b>{counts.knowledge.uncharted.toLocaleString()} not fully tabulated</b> cells. Stability is used exactly when <b>k ≤ n − 2</b>. Purple is a separate source-auditable Lean overlay; bright purple marks the exact benchmark model.</p>
    </div>
  );
}
