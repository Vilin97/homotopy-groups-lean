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
  declaration: string;
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
  degree_lattice_kind: string | null;
};
type FormalizationCell = {
  n: number;
  k: number;
  record_id: string;
  proof_declaration: string;
  proof_source: string;
};
type DegreeFormalizationCell = {
  n: number;
  m: number;
  record_id: string;
  proof_declaration: string;
  proof_source: string;
};
type FormalizationInventory = {
  source: string;
  records: FormalizationRecord[];
  lattice: {
    n_min: number;
    n_max: number;
    k_min: number;
    k_max: number;
    cells: FormalizationCell[];
  };
  degree_lattice: {
    n_min: number;
    n_max: number;
    m_min: number;
    m_max: number;
    cells: DegreeFormalizationCell[];
  };
};
type ViewMode = "degree" | "stem";
type Coordinate = { n: number; column: number };
type CanvasGeometry = { left: number; top: number; cell: number };

const stems = stableStemData.stems as StableStem[];
const sources = new Map(stableStemData.sources.map((source) => [source.source_id, source.url]));
const formalizationInventory = leaderboardData.formalization_inventory as FormalizationInventory;
const stemLattice = formalizationInventory.lattice;
const degreeLattice = formalizationInventory.degree_lattice;
const formalizationRecords = new Map(
  formalizationInventory.records.map((record) => [record.id, record]),
);
const stemFormalizationCells = new Map(
  stemLattice.cells.map((cell) => [`${cell.n}:${cell.k}`, cell]),
);
const degreeFormalizationCells = new Map(
  degreeLattice.cells.map((cell) => [`${cell.n}:${cell.m}`, cell]),
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
  if (isStable(n, k)) {
    const stem = stems[k];
    return stem ? (stem.is_exact ? "exact" : "partial") : "uncharted";
  }
  // Published 2-primary unstable computations in the review.
  if (k >= 21 && k <= 32) return "primary";
  if (k === 33 && ((n >= 2 && n <= 9) || (n >= 28 && n <= 34))) return "primary";
  if (k === 33 && n === 27) return "disputed";
  return "uncharted";
}

function knowledgeAtCoordinate(view: ViewMode, n: number, column: number): Knowledge {
  if (view === "degree" && column < n) return "exact";
  return knowledgeAt(n, view === "degree" ? column - n : column);
}

function formalizationAt(view: ViewMode, n: number, column: number): Formalization {
  const cell = (view === "degree" ? degreeFormalizationCells : stemFormalizationCells)
    .get(`${n}:${column}`);
  const record = cell ? formalizationRecords.get(cell.record_id) : undefined;
  if (!record) return null;
  const dualKernel = record.status === "dual_kernel_verified_reference";
  const kernelChecked = record.status === "lean_kernel_checked_local_source";
  const historical = record.status === "source_audited_historical";
  const exactMetricModel = (view === "degree"
    ? record.degree_lattice_kind ?? record.lattice_kind
    : record.lattice_kind) === "lean4_exact_metric_model";
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
    declaration: cell.proof_declaration,
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
  const [view, setView] = useState<ViewMode>("degree");
  const [selected, setSelected] = useState<Coordinate>({ n: 2, column: 1 });
  const [jumpN, setJumpN] = useState("2");
  const [jumpColumn, setJumpColumn] = useState("1");
  const [canvasWidth, setCanvasWidth] = useState(720);
  const [shown, setShown] = useState<Record<Knowledge, boolean>>({
    exact: true, partial: true, primary: true, disputed: true, uncharted: true,
  });
  const [showFormalizations, setShowFormalizations] = useState(true);
  const canvasRef = useRef<HTMLCanvasElement>(null);
  const canvasFrameRef = useRef<HTMLDivElement>(null);
  const geometryRef = useRef<CanvasGeometry>({ left: 34, top: 25, cell: 7 });
  const nMin = view === "degree" ? degreeLattice.n_min : stemLattice.n_min;
  const nMax = view === "degree" ? degreeLattice.n_max : stemLattice.n_max;
  const columnMin = view === "degree" ? degreeLattice.m_min : stemLattice.k_min;
  const columnMax = view === "degree" ? degreeLattice.m_max : stemLattice.k_max;
  const rowCount = nMax - nMin + 1;
  const columnCount = columnMax - columnMin + 1;

  const counts = useMemo(() => {
    const knowledge: Record<Knowledge, number> = {
      exact: 0, partial: 0, primary: 0, disputed: 0, uncharted: 0,
    };
    let formalized = 0;
    for (let n = nMin; n <= nMax; n += 1) {
      for (let column = columnMin; column <= columnMax; column += 1) {
        knowledge[knowledgeAtCoordinate(view, n, column)] += 1;
        if (formalizationAt(view, n, column)) formalized += 1;
      }
    }
    return { knowledge, formalized };
  }, [columnMax, columnMin, nMax, nMin, view]);

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
      for (let column = columnMin; column <= columnMax; column += 1) {
        const status = knowledgeAtCoordinate(view, n, column);
        const formalization = formalizationAt(view, n, column);
        const x = left + (column - columnMin) * cell + gap / 2;
        const y = top + row * cell + gap / 2;
        context.globalAlpha = shown[status] ? .97 : .08;
        context.fillStyle = knowledgeCopy[status].color;
        context.fillRect(x, y, cell - gap, cell - gap);
        if (formalization && showFormalizations) {
          context.globalAlpha = 1;
          const overlayColor = formalization.kind === "lean4-exact"
            ? "#d890ff"
            : formalization.kind === "lean4" ? "#9b7cff" : "#bca7ef";
          context.fillStyle = overlayColor;
          context.fillRect(x, y, cell - gap, cell - gap);
          context.strokeStyle = "#080b10";
          context.lineWidth = Math.max(.35, cell * .06);
          context.strokeRect(x, y, cell - gap, cell - gap);
        }
      }
    }
    context.globalAlpha = 1;
    const selectedX = left + (selected.column - columnMin) * cell + .5;
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
    for (let column = columnMin; column <= columnMax; column += 10) {
      context.fillText(String(column), left + (column - columnMin + .5) * cell, 15);
    }
    context.textAlign = "right";
    for (let n = 10; n <= nMax; n += 10) context.fillText(String(n), left - 6, top + (n - nMin + .8) * cell);
    context.fillStyle = "#4fdda8";
    context.font = "italic 11px Georgia, serif";
    context.textAlign = "left";
    context.fillText("n", 10, 14);
    context.textAlign = "right";
    context.fillText(view === "degree" ? "m →" : "k →", canvasWidth - 8, height - 8);
  }, [canvasWidth, columnCount, columnMax, columnMin, nMax, nMin, rowCount, selected, shown, showFormalizations, view]);

  const selectCoordinate = (coordinate: Coordinate) => {
    setSelected(coordinate);
    setJumpN(String(coordinate.n));
    setJumpColumn(String(coordinate.column));
  };
  const selectView = (nextView: ViewMode) => {
    setView(nextView);
    const coordinate = nextView === "degree"
      ? { n: 2, column: 1 }
      : { n: 1, column: 0 };
    setSelected(coordinate);
    setJumpN(String(coordinate.n));
    setJumpColumn(String(coordinate.column));
  };
  const locate = (event: FormEvent) => {
    event.preventDefault();
    const n = Math.min(nMax, Math.max(nMin, Number.parseInt(jumpN, 10) || nMin));
    const column = Math.min(
      columnMax,
      Math.max(columnMin, Number.parseInt(jumpColumn, 10) || columnMin),
    );
    selectCoordinate({ n, column });
    canvasRef.current?.focus();
  };
  const coordinateFromPointer = (event: PointerEvent<HTMLCanvasElement>): Coordinate | null => {
    const bounds = event.currentTarget.getBoundingClientRect();
    const scaleX = canvasWidth / bounds.width;
    const scaleY = Number.parseFloat(event.currentTarget.style.height) / bounds.height;
    const { left, top, cell } = geometryRef.current;
    const columnIndex = Math.floor(((event.clientX - bounds.left) * scaleX - left) / cell);
    const column = columnMin + columnIndex;
    const row = Math.floor(((event.clientY - bounds.top) * scaleY - top) / cell);
    if (column < columnMin || column > columnMax || row < 0 || row >= rowCount) return null;
    return { n: nMin + row, column };
  };
  const inspectPointer = (event: PointerEvent<HTMLCanvasElement>) => {
    const coordinate = coordinateFromPointer(event);
    if (coordinate && (coordinate.n !== selected.n || coordinate.column !== selected.column)) selectCoordinate(coordinate);
  };
  const moveWithKeys = (event: KeyboardEvent<HTMLCanvasElement>) => {
    const movement: Record<string, Coordinate> = {
      ArrowUp: { n: Math.max(nMin, selected.n - 1), column: selected.column },
      ArrowDown: { n: Math.min(nMax, selected.n + 1), column: selected.column },
      ArrowLeft: { n: selected.n, column: Math.max(columnMin, selected.column - 1) },
      ArrowRight: { n: selected.n, column: Math.min(columnMax, selected.column + 1) },
    };
    if (!movement[event.key]) return;
    event.preventDefault();
    selectCoordinate(movement[event.key]);
  };

  const degree = view === "degree" ? selected.column : selected.n + selected.column;
  const stemIndex = degree - selected.n;
  const status = knowledgeAtCoordinate(view, selected.n, selected.column);
  const formalization = formalizationAt(view, selected.n, selected.column);
  const stem = stems[stemIndex];
  const belowDiagonal = degree < selected.n;
  const stable = stemIndex >= 0 && isStable(selected.n, stemIndex);
  const sourceUrl = stable
    ? stem?.source_refs.map((ref) => sources.get(ref.source_id)).find(Boolean)
    : siteAsset("/reports/homotopy-groups-of-spheres-literature-review.pdf");
  const obviousGroup = selected.n === 1
    ? (degree === 1 ? "ℤ" : "0")
    : belowDiagonal
      ? "0"
      : stemIndex === 0 || (selected.n === 2 && stemIndex === 1)
      ? "ℤ"
      : stable && status === "exact"
        ? formatGroup(stem.group)
        : null;

  return (
    <div className="atlas-card">
      <div className="atlas-view-switch" aria-label="Lattice coordinate view" role="group">
        <button aria-pressed={view === "degree"} onClick={() => selectView("degree")} type="button">
          Lean coverage · π<sub>m</sub>(S<sup>n</sup>)
          <strong>{degreeLattice.cells.length.toLocaleString()} purple cells</strong>
        </button>
        <button aria-pressed={view === "stem"} onClick={() => selectView("stem")} type="button">
          Stable stems · π<sub>n+k</sub>(S<sup>n</sup>)
          <strong>{stemLattice.cells.length.toLocaleString()} purple cells</strong>
        </button>
      </div>
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
          <label><span>{view === "degree" ? "m" : "k"}</span><input aria-label={view === "degree" ? "Homotopy degree m" : "Stem k"} max={columnMax} min={columnMin} onChange={(event) => setJumpColumn(event.target.value)} type="number" value={jumpColumn} /></label>
          <button type="submit">Locate</button>
        </form>
      </div>
      <div className="atlas-main">
        <div className="lattice-wrap">
          <div className="lattice-axis-title"><span className="math-expression">{view === "degree" ? <>π<sub>m</sub>(S<sup>n</sup>)</> : <>π<sub>n+k</sub>(S<sup>n</sup>)</>}</span><strong>hover · click · arrow keys</strong></div>
          <p className="sr-only" id="lattice-instructions">Use the arrow keys to inspect adjacent cells, or enter coordinates in the locate form.</p>
          <div className="canvas-frame" ref={canvasFrameRef}>
            <canvas
              aria-describedby="lattice-instructions"
              aria-label={`Interactive evidence lattice. Selected pi_${degree}(S^${selected.n}): ${knowledgeCopy[status].short}${formalization ? `, ${formalization.accessibleLabel}` : ""}.`}
              className="lattice-canvas" onClick={inspectPointer} onKeyDown={moveWithKeys}
              onPointerMove={inspectPointer} ref={canvasRef} tabIndex={0}
            >Use the coordinate form to inspect the evidence lattice.</canvas>
          </div>
          <div className="k-axis"><span>n = {nMin}…{nMax}</span><strong>{view === "degree" ? `m = ${columnMin}…${columnMax}` : `k = m − n = ${columnMin}…${columnMax}`}</strong></div>
        </div>
        <aside className={`coordinate-detail ${status}${formalization ? " formalized" : ""}`} aria-live="polite">
          <div className="detail-status"><i aria-hidden="true" style={{ background: knowledgeCopy[status].color }} /> {knowledgeCopy[status].label}</div>
          {formalization && <div className="formalization-badge">{formalization.badge}</div>}
          <h3 className="math-expression">π<sub>{degree}</sub>(S<sup>{selected.n}</sup>)</h3>
          <div className="coordinate-pair"><span>n = {selected.n}</span><span>m = {degree}</span><span>k = {stemIndex}</span></div>
          {obviousGroup && <div className="group-value"><span>integral group</span><strong>{obviousGroup}</strong></div>}
          {status === "exact" && !obviousGroup && stable && <div className="group-value"><span className="math-expression">≅ π<sub>{stemIndex}</sub>(𝕊)</span><strong>{formatGroup(stem.group)}</strong></div>}
          {status === "exact" && !obviousGroup && !stable && <p>The complete integral group is tabulated in Toda&apos;s 0–19 stem tables or the Mimura–Toda 20-stem computation reproduced in the review.</p>}
          {status === "partial" && <><div className="group-value"><span>published full groups</span><strong>{stem.alternatives?.length ?? 0} alternatives</strong></div><div className="alternatives">{stem.alternatives?.map((alternative, index) => <span key={alternative.alternative_id}><b>{String.fromCharCode(65 + index)}</b>{formatGroup(alternative.group)}</span>)}</div><p>{stem.note}</p></>}
          {status === "primary" && <><div className="group-value"><span>computed component</span><strong>2-primary</strong></div><p>The 2-primary component is tabulated, but this view does not claim a complete integral group.</p></>}
          {status === "disputed" && <><div className="group-value"><span>33-stem</span><strong>conflicting values</strong></div><p>The literature review records incompatible published values at n = 27. This cell stays visibly disputed.</p></>}
          {status === "uncharted" && <><div className="group-value"><span>review coverage</span><strong>not fully tabulated</strong></div><p>Gray means the attached review does not provide a complete integral value here—not that mathematics knows nothing about the group.</p></>}
          {formalization && <p className="formalization-note">{formalization.note} It does not change the literature evidence class beneath it.</p>}
          {formalization
            ? <div className="proof-witness"><span>Exact Lean theorem</span><a href={formalization.source}><code>{formalization.declaration}</code> ↗</a></div>
            : <div className="proof-witness missing"><span>Lean theorem</span><strong>not formalized yet</strong></div>}
          <div className="detail-links">
            {formalization && <a href={formalizationInventory.source}>full inventory ↗</a>}
            {sourceUrl && <a href={sourceUrl}>mathematical source ↗</a>}
          </div>
        </aside>
      </div>
      <p className="atlas-scope">Audited {rowCount} × {columnCount} {view === "degree" ? "absolute-degree" : "stem"} view: <b>{counts.knowledge.exact.toLocaleString()} exact integral</b>, <b>{counts.knowledge.partial.toLocaleString()} published-alternative</b>, <b>{counts.knowledge.primary.toLocaleString()} exact 2-primary-only</b>, <b>{counts.knowledge.disputed.toLocaleString()} disputed</b>, and <b>{counts.knowledge.uncharted.toLocaleString()} not fully tabulated</b> cells. {view === "degree" ? <>The purple triangle is the kernel-checked theorem <b>1 ≤ m &lt; n ⟹ πₘ(Sⁿ) = 0</b>; switch to stable stems for the full k = 0…108 audit.</> : <>Stability is used exactly when <b>k ≤ n − 2</b> and a complete integral stem is in the audited registry.</>} Purple is a separate source-auditable Lean overlay; bright purple marks the exact benchmark model.</p>
    </div>
  );
}
