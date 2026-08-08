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
import stableStemData from "../public/data/stable-stems.json";

type Decomposition = {
  free_rank: number;
  torsion_invariant_factors: number[];
};

type Group = {
  integral_decomposition: Decomposition;
};

type StableStem = {
  stem: number;
  is_exact: boolean;
  group?: Group;
  alternatives?: Array<{ alternative_id: string; group: Group }>;
  note?: string;
  source_refs: Array<{ source_id: string }>;
};

type Knowledge = "formalized" | "exact" | "partial" | "uncharted";
type Coordinate = { n: number; k: number };
type CanvasGeometry = { left: number; top: number; cell: number };

const stems = stableStemData.stems as StableStem[];
const sources = new Map(stableStemData.sources.map((source) => [source.source_id, source.url]));
const nMin = 1;
const nMax = 92;
const kMax = 90;
const rowCount = nMax - nMin + 1;
const columnCount = kMax + 1;

const statusCopy: Record<Knowledge, { label: string; short: string; color: string }> = {
  formalized: { label: "Lean verified", short: "formalized and kernel-verified", color: "#aa8cff" },
  exact: { label: "Fully known", short: "exact group", color: "#4fdda8" },
  partial: { label: "Some information", short: "published alternatives", color: "#ffb75e" },
  uncharted: { label: "Uncharted", short: "no group value recorded", color: "#303947" },
};

function knowledgeAt(n: number, k: number): Knowledge {
  if (n === 1 && k === 0) return "formalized";
  if (n === 2 && k === 1) return "exact";
  if (k > n - 2) return "uncharted";
  return stems[k]?.is_exact ? "exact" : "partial";
}

function factsAt(n: number, k: number): string[] {
  if (n === 1 || k === 0) return [];
  const facts: string[] = [];
  if (n % 2 === 1) facts.push("|π| < ∞");
  if (n % 2 === 0 && k !== n - 1) facts.push("|π| < ∞");
  if (n % 2 === 0 && k === n - 1) facts.push("rank = 1");
  if (n === 2 || n === 3) facts.push("π ≠ 0");
  return facts;
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
    formalized: true,
    exact: true,
    partial: true,
    uncharted: true,
  });
  const canvasRef = useRef<HTMLCanvasElement>(null);
  const canvasFrameRef = useRef<HTMLDivElement>(null);
  const geometryRef = useRef<CanvasGeometry>({ left: 34, top: 25, cell: 7 });

  const counts = useMemo(() => {
    const total: Record<Knowledge, number> = { formalized: 0, exact: 0, partial: 0, uncharted: 0 };
    for (let n = nMin; n <= nMax; n += 1) {
      for (let k = 0; k <= kMax; k += 1) total[knowledgeAt(n, k)] += 1;
    }
    return total;
  }, []);

  useEffect(() => {
    const frame = canvasFrameRef.current;
    if (!frame) return;
    const observer = new ResizeObserver(([entry]) => setCanvasWidth(Math.max(280, Math.floor(entry.contentRect.width))));
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
    const plotHeight = cell * rowCount;
    const height = top + plotHeight + bottom;
    geometryRef.current = { left, top, cell };

    canvas.width = Math.round(canvasWidth * ratio);
    canvas.height = Math.round(height * ratio);
    canvas.style.width = `${canvasWidth}px`;
    canvas.style.height = `${height}px`;
    context.setTransform(ratio, 0, 0, ratio, 0, 0);
    context.clearRect(0, 0, canvasWidth, height);
    context.fillStyle = "#080b10";
    context.fillRect(0, 0, canvasWidth, height);

    const gap = Math.max(.35, Math.min(1.2, cell * .12));
    for (let row = 0; row < rowCount; row += 1) {
      const n = nMin + row;
      for (let k = 0; k <= kMax; k += 1) {
        const status = knowledgeAt(n, k);
        context.globalAlpha = shown[status] ? .96 : .08;
        context.fillStyle = statusCopy[status].color;
        context.fillRect(left + k * cell + gap / 2, top + row * cell + gap / 2, cell - gap, cell - gap);
      }
    }
    context.globalAlpha = 1;

    context.strokeStyle = "#f8f6ef";
    context.lineWidth = Math.max(1.5, cell * .18);
    context.strokeRect(
      left + selected.k * cell + 1,
      top + (selected.n - nMin) * cell + 1,
      Math.max(1, cell - 2),
      Math.max(1, cell - 2),
    );

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
  }, [canvasWidth, selected, shown]);

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
  const stem = stems[selected.k];
  const isLeanVerifiedCell = selected.n === 1 && selected.k === 0;
  const isHopfCell = selected.n === 2 && selected.k === 1;
  const coordinateFacts = factsAt(selected.n, selected.k);
  const sourceUrl = isLeanVerifiedCell
    ? "https://github.com/Vilin97/homotopy-groups-lean/blob/main/results/issue-dispatch-run-31188000114-attempt-1.json"
    : isHopfCell
      ? "https://pi.math.cornell.edu/~hatcher/AT/AT.pdf"
      : stem?.source_refs.map((ref) => sources.get(ref.source_id)).find(Boolean);

  return (
    <div className="atlas-card">
      <div className="atlas-toolbar">
        <div className="knowledge-legend" aria-label="Toggle lattice knowledge classes">
          {(Object.keys(statusCopy) as Knowledge[]).map((key) => (
            <button
              aria-pressed={shown[key]}
              className={`legend-control ${key}`}
              key={key}
              onClick={() => setShown((current) => ({ ...current, [key]: !current[key] }))}
              type="button"
            >
              <i aria-hidden="true" />
              <span>{statusCopy[key].label}</span>
              <strong>{counts[key].toLocaleString()}</strong>
            </button>
          ))}
        </div>
        <form className="coordinate-jump" onSubmit={locate}>
          <label><span>n</span><input aria-label="Sphere dimension n" max={nMax} min={nMin} onChange={(event) => setJumpN(event.target.value)} type="number" value={jumpN} /></label>
          <label><span>k</span><input aria-label="Stem k" max={kMax} min="0" onChange={(event) => setJumpK(event.target.value)} type="number" value={jumpK} /></label>
          <button type="submit">Locate</button>
        </form>
      </div>

      <div className="atlas-main">
        <div className="lattice-wrap">
          <div className="lattice-axis-title"><span>π<sub>n+k</sub>(S<sup>n</sup>)</span><strong>hover · click · arrow keys</strong></div>
          <div className="canvas-frame" ref={canvasFrameRef}>
            <canvas
              aria-label={`Interactive knowledge lattice. Selected π_${selected.n + selected.k}(S^${selected.n}): ${statusCopy[status].short}.`}
              className="lattice-canvas"
              onClick={inspectPointer}
              onKeyDown={moveWithKeys}
              onPointerMove={inspectPointer}
              ref={canvasRef}
              tabIndex={0}
            />
          </div>
          <div className="k-axis"><span>n = 1…92</span><strong>k = m − n = 0…90</strong></div>
        </div>

        <aside className={`coordinate-detail ${status}`} aria-live="polite">
          <div className="detail-status"><i aria-hidden="true" /> {statusCopy[status].label}</div>
          <h3>π<sub>{selected.n + selected.k}</sub>(S<sup>{selected.n}</sup>)</h3>
          <div className="coordinate-pair"><span>n = {selected.n}</span><span>k = {selected.k}</span></div>

          {status === "formalized" && (
            <><div className="group-value"><span>Comparator + 2 kernels</span><strong>ℤ</strong></div><p>The proof of π<sub>1</sub>(S<sup>1</sup>) ≅ ℤ passed Comparator, Lean&apos;s kernel, and nanoda. Purple is reserved for recorded verified proofs.</p></>
          )}

          {status === "exact" && (
            <>
              <div className="group-value"><span>{isHopfCell ? "Hopf fibration" : <>≅ π<sub>{selected.k}</sub><sup>S</sup> ≅</>}</span><strong>{isHopfCell ? "ℤ" : formatGroup(stem.group)}</strong></div>
              {isHopfCell ? <p>The explicit unstable exception: π<sub>3</sub>(S<sup>2</sup>) ≅ ℤ, not the stable first stem ℤ/2.</p> : <p>Stable because <b>k ≤ n − 2</b>. The abstract additive group is exact in the published registry.</p>}
            </>
          )}

          {status === "partial" && (
            <>
              <div className="group-value"><span>≅ π<sub>{selected.k}</sub><sup>S</sup></span><strong>{stem.alternatives?.length ?? 0} possibilities</strong></div>
              <div className="alternatives">{stem.alternatives?.map((alternative, index) => <span key={alternative.alternative_id}><b>{String.fromCharCode(65 + index)}</b>{formatGroup(alternative.group)}</span>)}</div>
              <p>{stem.note}</p>
            </>
          )}

          {status === "uncharted" && (
            <>
              <div className="group-value"><span>k &gt; n − 2</span><strong>unstable</strong></div>
              <p>No exact group value is recorded for this coordinate in the benchmark yet. This is not a claim that the literature contains no information.</p>
              {coordinateFacts.length > 0 && <div className="fact-badges" aria-label="Known qualitative facts">{coordinateFacts.map((fact) => <span key={fact}>{fact}</span>)}</div>}
            </>
          )}

          {sourceUrl && status !== "uncharted" ? <a href={sourceUrl}>{status === "formalized" ? "verification record ↗" : "primary source ↗"}</a> : <a href="https://github.com/Vilin97/homotopy-groups-lean/issues/new/choose">add a result ↗</a>}
        </aside>
      </div>

      <p className="atlas-scope">Classification is benchmark-scoped. Purple means an actual comparator-verified Lean proof. In the stable range <b>k ≤ n − 2</b>, the cell inherits the published value of π<sub>k</sub><sup>S</sup>; elsewhere, gray means “not classified here.”</p>
    </div>
  );
}
