"use client";

import {
  type FormEvent,
  type KeyboardEvent,
  type MouseEvent,
  useEffect,
  useMemo,
  useRef,
  useState,
} from "react";
import frontierData from "../public/data/extended-frontiers.json";
import { siteAsset } from "./site";

type IntegralStem = { stem: number; group: string; status: "exact" | "published_alternatives" };
type ThreePrimaryStem = {
  stem: number;
  group: string;
  image_j_or_degree_zero: string;
  non_j_component: string;
  non_j_generators: string;
  nonzero: boolean;
  notes: string;
};
type FivePrimaryEntry = {
  stem: number;
  transcription: string;
  uncertain: boolean;
  quarantined: boolean;
  transcription_status: string;
  source_url: string;
};
type ImageJEntry = { prime: string; family_type: string; group: string; formula_case: string; status: string };
type ImageJStem = { stem: number; entries: ImageJEntry[] };
type PeriodicRow = {
  row_label: string;
  cyclic_order: string;
  representative: string;
  filtration_range: string;
  family_count: number;
  proof_method: string;
  source_url: string;
};
type PeriodicResidue = { residue: number; family_count: number; rows: PeriodicRow[] };

const firstStem = frontierData.display.first_stem;
const lastStem = frontierData.display.last_stem;
const threePrimaryLastStem =
  frontierData.three_primary.coverage.positive_stem_primary_components.last;
const fivePrimaryLastStem = frontierData.five_primary_non_j.coverage.last;
const imageJLedgerLastStem = frontierData.image_j_v1.ledger.last;
const heightTwoPeriod = frontierData.height_two_two_primary.period;
const integralStems = frontierData.integral.stems as IntegralStem[];
const threePrimaryStems = frontierData.three_primary.stems as ThreePrimaryStem[];
const fivePrimaryEntries = frontierData.five_primary_non_j.entries as FivePrimaryEntry[];
const imageJStems = frontierData.image_j_v1.stems as ImageJStem[];
const periodicResidues = frontierData.height_two_two_primary.residues as PeriodicResidue[];

const integralByStem = new Map(integralStems.map((row) => [row.stem, row]));
const threeByStem = new Map(threePrimaryStems.map((row) => [row.stem, row]));
const fiveByStem = new Map(fivePrimaryEntries.map((row) => [row.stem, row]));
const imageJByStem = new Map(imageJStems.map((row) => [row.stem, row]));
const periodicByResidue = new Map(periodicResidues.map((row) => [row.residue, row]));

const plotWidth = 1180;
const plotHeight = 306;
const plotLeft = 154;
const plotRight = 20;
const plotSpan = plotWidth - plotLeft - plotRight;
const laneCenters = [55, 105, 155, 205, 255];

function xFor(stem: number): number {
  return plotLeft + ((stem - firstStem) / (lastStem - firstStem)) * plotSpan;
}

function clampStem(value: number): number {
  return Math.min(lastStem, Math.max(firstStem, value));
}

export function Frontiers() {
  const [selected, setSelected] = useState(91);
  const [jumpStem, setJumpStem] = useState("91");
  const canvasRef = useRef<HTMLCanvasElement>(null);
  const scrollRef = useRef<HTMLDivElement>(null);

  const selectedFacts = useMemo(() => ({
    integral: integralByStem.get(selected),
    three: threeByStem.get(selected),
    five: fiveByStem.get(selected),
    imageJ: imageJByStem.get(selected),
    periodic: periodicByResidue.get(
      ((selected % heightTwoPeriod) + heightTwoPeriod) % heightTwoPeriod,
    ),
  }), [selected]);

  useEffect(() => {
    const canvas = canvasRef.current;
    if (!canvas) return;
    const context = canvas.getContext("2d");
    if (!context) return;
    const ratio = window.devicePixelRatio || 1;
    canvas.width = plotWidth * ratio;
    canvas.height = plotHeight * ratio;
    canvas.style.width = `${plotWidth}px`;
    canvas.style.height = `${plotHeight}px`;
    context.setTransform(ratio, 0, 0, ratio, 0, 0);
    context.clearRect(0, 0, plotWidth, plotHeight);
    context.fillStyle = "#080b10";
    context.fillRect(0, 0, plotWidth, plotHeight);

    context.font = "9px ui-monospace, SFMono-Regular, Menlo, monospace";
    context.textAlign = "center";
    for (let stem = firstStem; stem <= lastStem; stem += 100) {
      const x = xFor(stem);
      context.strokeStyle = stem % 500 === 0 ? "#364152" : "#202936";
      context.lineWidth = 1;
      context.beginPath();
      context.moveTo(x + .5, 28);
      context.lineTo(x + .5, 278);
      context.stroke();
      context.fillStyle = "#7f8b9d";
      context.fillText(String(stem), x, 17);
    }

    const labels = [
      ["integral additive", "complete group"],
      ["3-local / primary", "complete additive"],
      ["5-primary non-J", "class ledger"],
      ["image J / v₁", "closed formula"],
      ["height two at 2", "class families"],
    ];
    context.textAlign = "left";
    labels.forEach(([label, scope], index) => {
      context.fillStyle = "#d5dae1";
      context.font = "10px ui-monospace, SFMono-Regular, Menlo, monospace";
      context.fillText(label, 12, laneCenters[index] - 2);
      context.fillStyle = "#8d98a8";
      context.font = "10px ui-monospace, SFMono-Regular, Menlo, monospace";
      context.fillText(scope, 12, laneCenters[index] + 12);
      context.strokeStyle = "#222b38";
      context.beginPath();
      context.moveTo(plotLeft, laneCenters[index] + 21.5);
      context.lineTo(plotWidth - plotRight, laneCenters[index] + 21.5);
      context.stroke();
    });

    const cellWidth = Math.max(1, plotSpan / 1001);
    for (const row of integralStems) {
      context.fillStyle = row.status === "exact" ? "#4fdda8" : "#ffb75e";
      context.fillRect(xFor(row.stem), laneCenters[0] - 10, cellWidth + .25, 20);
    }

    context.fillStyle = "rgba(93,169,214,.28)";
    context.fillRect(
      xFor(firstStem), laneCenters[1] - 10,
      xFor(threePrimaryLastStem) - xFor(firstStem) + cellWidth, 20,
    );
    for (const row of threePrimaryStems) {
      if (!row.nonzero) continue;
      context.fillStyle = "#70c7f2";
      context.fillRect(xFor(row.stem), laneCenters[1] - 10, Math.max(1.35, cellWidth), 20);
    }

    context.strokeStyle = "rgba(239,190,92,.58)";
    context.setLineDash([4, 3]);
    context.strokeRect(
      xFor(firstStem), laneCenters[2] - 10,
      xFor(fivePrimaryLastStem) - xFor(firstStem), 20,
    );
    context.setLineDash([]);
    for (const row of fivePrimaryEntries) {
      context.strokeStyle = row.uncertain ? "#f08096" : row.quarantined ? "#ff745f" : "#efbe5c";
      context.lineWidth = row.uncertain || row.quarantined ? 2 : 1;
      const x = xFor(row.stem) + .5;
      context.beginPath();
      context.moveTo(x, laneCenters[2] - 10);
      context.lineTo(x, laneCenters[2] + 10);
      context.stroke();
      if (row.uncertain || row.quarantined) {
        context.beginPath();
        context.moveTo(x - 3, laneCenters[2] + 10);
        context.lineTo(x + 3, laneCenters[2] - 10);
        context.stroke();
      }
    }

    context.strokeStyle = "#78d8da";
    context.lineWidth = 2;
    context.beginPath();
    context.moveTo(xFor(firstStem), laneCenters[3]);
    context.lineTo(xFor(imageJLedgerLastStem), laneCenters[3]);
    context.stroke();
    for (const row of imageJStems) {
      context.fillStyle = "#b1ffff";
      context.fillRect(xFor(row.stem), laneCenters[3] - 5, Math.max(1, cellWidth), 10);
    }
    context.fillStyle = "#78d8da";
    context.font = "bold 11px ui-monospace, monospace";
    context.fillText("→ ∞", plotWidth - 18, laneCenters[3] - 12);

    for (const residue of periodicResidues) {
      for (let stem = residue.residue; stem <= lastStem; stem += heightTwoPeriod) {
        const height = 7 + Math.min(16, residue.family_count);
        context.strokeStyle = "#e8896b";
        context.lineWidth = 1.4;
        context.beginPath();
        context.moveTo(xFor(stem) + .5, laneCenters[4] + height / 2);
        context.lineTo(xFor(stem) + .5, laneCenters[4] - height / 2);
        context.stroke();
      }
    }

    const selectedX = xFor(selected) + .5;
    context.strokeStyle = "#f3f0e8";
    context.lineWidth = 3;
    context.beginPath();
    context.moveTo(selectedX, 27);
    context.lineTo(selectedX, 279);
    context.stroke();
    context.strokeStyle = "#4fdda8";
    context.lineWidth = 1;
    context.beginPath();
    context.moveTo(selectedX, 27);
    context.lineTo(selectedX, 279);
    context.stroke();
    context.fillStyle = "#4fdda8";
    context.textAlign = "center";
    context.font = "bold 9px ui-monospace, monospace";
    context.fillText(`stem ${selected}`, selectedX, 296);
  }, [selected]);

  const chooseStem = (stem: number) => {
    const next = clampStem(stem);
    setSelected(next);
    setJumpStem(String(next));
    window.requestAnimationFrame(() => {
      const viewport = scrollRef.current;
      if (!viewport) return;
      const target = xFor(next) - viewport.clientWidth / 2;
      viewport.scrollTo({
        left: Math.max(0, Math.min(plotWidth - viewport.clientWidth, target)),
        behavior: "smooth",
      });
    });
  };
  const locate = (event: FormEvent) => {
    event.preventDefault();
    chooseStem(Number.parseInt(jumpStem, 10) || 0);
    canvasRef.current?.focus();
  };
  const inspectPointer = (event: MouseEvent<HTMLCanvasElement>) => {
    const bounds = event.currentTarget.getBoundingClientRect();
    const logicalX = ((event.clientX - bounds.left) / bounds.width) * plotWidth;
    const stem = Math.round(
      firstStem + ((logicalX - plotLeft) / plotSpan) * (lastStem - firstStem),
    );
    if (stem >= firstStem && stem <= lastStem) chooseStem(stem);
  };
  const moveWithKeys = (event: KeyboardEvent<HTMLCanvasElement>) => {
    const moves: Record<string, number> = {
      ArrowLeft: selected - 1,
      ArrowRight: selected + 1,
      PageUp: selected + 10,
      PageDown: selected - 10,
      Home: firstStem,
      End: lastStem,
    };
    if (moves[event.key] === undefined) return;
    event.preventDefault();
    chooseStem(moves[event.key]);
  };

  const periodicRows = selectedFacts.periodic?.rows ?? [];
  const periodicMethods = Array.from(new Set(periodicRows.map((row) => row.proof_method)));
  const report = siteAsset("/reports/comprehensive-2026/");
  const frontierCsv = siteAsset("/reports/comprehensive-2026/data/computation_frontiers_2026.csv");
  const audit = "https://github.com/Vilin97/homotopy-groups-lean/blob/main/research/comprehensive-handoff-audit.md";

  return (
    <div className="frontier-card">
      <p className="frontier-warning"><strong>Read the shapes, not just the colors.</strong> {frontierData.interpretive_rule}</p>
      <div className="frontier-toolbar">
        <div className="frontier-legend" aria-label="Stable frontier mark types">
          <span><i className="coverage" />coverage band</span>
          <span><i className="entry" />nonzero or named entry</span>
          <span><i className="periodic" />periodic existence</span>
          <span><i className="uncertain" />source “?”</span>
          <span><i className="quarantined" />package defect</span>
        </div>
        <form className="frontier-jump" onSubmit={locate}>
          <label><span>stem</span><input aria-label="Stable stem" max={lastStem} min={firstStem}
            onChange={(event) => setJumpStem(event.target.value)} type="number" value={jumpStem} /></label>
          <button type="submit">Locate</button>
        </form>
      </div>
      <p className="sr-only" id="frontier-instructions">
        Use Left and Right Arrow to move one stem, Page Up and Page Down to move ten,
        or Home and End to select the first and last rendered stems.
      </p>
      <div className="frontier-scroll" aria-label="Horizontally scrollable stable frontier plot" ref={scrollRef}>
        <canvas
          aria-describedby="frontier-instructions"
          aria-label="Stable frontier stem"
          aria-valuemax={lastStem}
          aria-valuemin={firstStem}
          aria-valuenow={selected}
          aria-valuetext={`Stable stem ${selected}`}
          className="frontier-canvas" onClick={inspectPointer} onKeyDown={moveWithKeys}
          ref={canvasRef} role="slider" tabIndex={0}
        >Use the stem input to inspect the stable frontier atlas.</canvas>
      </div>
      <div className="frontier-selected">
        <div className="frontier-selected-head">
          <span>SELECTED STABLE STEM</span><strong>{selected}</strong>
          <small>five claims, kept separate</small>
        </div>
        <p className="sr-only" aria-atomic="true" aria-live="polite">
          Selected stable stem {selected}.
        </p>
        <div className="frontier-facts">
          <article className={selectedFacts.integral?.status === "published_alternatives" ? "partial" : "integral"}>
            <span>Integral additive</span>
            <strong>{selectedFacts.integral
              ? selectedFacts.integral.status === "exact" ? "Exact group" : "Published alternatives"
              : "No complete row"}</strong>
            <p>{selectedFacts.integral?.group ?? "The consecutive integral ledger stops at stem 90."}</p>
          </article>
          <article className="three-primary">
            <span>3-local / 3-primary additive</span>
            <strong>{selectedFacts.three
              ? selected === 0 ? "Degree-zero 3-local group" : "Exact component"
              : "Outside exact range"}</strong>
            <p>{selectedFacts.three
              ? `${selectedFacts.three.group}${selectedFacts.three.group === "0" ? " (an exact zero)" : ""}`
              : `The complete positive-stem 3-primary table ends at stem ${threePrimaryLastStem}.`}</p>
            {selectedFacts.three?.non_j_generators && <small>{selectedFacts.three.non_j_generators}</small>}
          </article>
          <article className={selectedFacts.five?.uncertain
            ? "uncertain" : selectedFacts.five?.quarantined ? "quarantined" : "five-primary"}>
            <span>5-primary non-J</span>
            <strong>{selectedFacts.five
              ? selectedFacts.five.uncertain ? "Source-marked ?"
                : selectedFacts.five.quarantined ? "Transcription quarantined" : "Named ledger entry"
              : selected <= fivePrimaryLastStem ? "No entry listed" : "Beyond rendered ledger"}</strong>
            <p>{selectedFacts.five?.quarantined
              ? "The package extraction is visibly damaged here; consult Ravenel Table A3.3."
              : selectedFacts.five?.transcription ?? (selected <= fivePrimaryLastStem
              ? "This is not a claim that the 5-primary group is zero."
              : "The source ledger displayed here ends at stem 999.")}</p>
          </article>
          <article className="image-j">
            <span>Image J / v₁</span>
            <strong>All-stem formula</strong>
            <p>{selectedFacts.imageJ
              ? selectedFacts.imageJ.entries.map((entry) => `p=${entry.prime}: ${entry.group}`).join(" · ")
              : "No nonzero instantiated height-one entry at this stem."}</p>
          </article>
          <article className="height-two">
            <span>Height two at 2</span>
            <strong>{selectedFacts.periodic
              ? `${selectedFacts.periodic.family_count} period-192 families`
              : "No catalogued residue"}</strong>
            <p>{selectedFacts.periodic
              ? `Residue ${selectedFacts.periodic.residue} mod ${heightTwoPeriod}. ${periodicMethods.join("; ")}.`
              : "Absence of a tick is not a vanishing theorem."}</p>
          </article>
        </div>
      </div>
      <div className="frontier-links">
        <span>Audited overlay: current Ravenel edition · corrected v₁ exception · detector split · quarantined extraction defects</span>
        <a href={report}>read the comprehensive report ↗</a>
        <a href={audit}>read the correction log ↗</a>
        <a href={frontierCsv}>download frontier CSV ↗</a>
      </div>
    </div>
  );
}
