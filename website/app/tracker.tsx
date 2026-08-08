"use client";

import { useEffect, useMemo, useState } from "react";
import initialTracker from "../public/data/tracker.json";

type Status = "verified" | "formalization" | "computation" | "conjecture" | "provisional";
type Entry = {
  id: string;
  title: string;
  family: string;
  knowledge_status: string;
  formalization_status: string;
  source: string | null;
};

const liveTrackerUrl =
  "https://raw.githubusercontent.com/Vilin97/homotopy-groups-lean/main/website/public/data/tracker.json";

const filters: Array<{ value: "all" | Status; label: string }> = [
  { value: "all", label: "All" },
  { value: "verified", label: "Verified" },
  { value: "formalization", label: "Lean open" },
  { value: "computation", label: "Compute" },
  { value: "conjecture", label: "Conjectures" },
];

function statusFor(entry: Entry): Status {
  if (["comparator_verified", "maintained_test"].includes(entry.formalization_status)) return "verified";
  if (entry.knowledge_status === "formalized_upstream") return "verified";
  if (entry.knowledge_status.startsWith("open_computation")) return "computation";
  if (entry.knowledge_status.includes("conjecture")) return "conjecture";
  if (entry.knowledge_status.includes("provisional")) return "provisional";
  return "formalization";
}

function labelFor(entry: Entry): string {
  if (entry.formalization_status === "comparator_verified") return "Comparator verified";
  if (entry.formalization_status === "maintained_test") return "Maintained test";
  if (entry.knowledge_status.startsWith("open_computation")) return "Open computation";
  if (entry.knowledge_status.includes("conjecture")) return "Conjecture";
  if (entry.knowledge_status.includes("provisional")) return "Preprint claim";
  if (entry.knowledge_status === "native_consequence") return "Native consequence";
  if (entry.knowledge_status === "derivable_from_pinned_mathlib") return "Reference-solvable";
  if (entry.knowledge_status === "foundation_blocked") return "Foundation blocked";
  if (entry.knowledge_status === "formalized_upstream") return "Formalized upstream";
  if (entry.knowledge_status === "known_result/exact") return "Exact value · open in Lean";
  return "Known theorem · open in Lean";
}

export function Tracker() {
  const [entries, setEntries] = useState<Entry[]>(initialTracker.entries as Entry[]);
  const [filter, setFilter] = useState<"all" | Status>("all");
  const [query, setQuery] = useState("");
  const [limit, setLimit] = useState(8);

  useEffect(() => {
    fetch(`${liveTrackerUrl}?v=${Date.now()}`, { cache: "no-store" })
      .then((response) => response.ok ? response.json() : Promise.reject(new Error("tracker fetch failed")))
      .then((payload: { entries?: Entry[] }) => {
        if (Array.isArray(payload.entries)) setEntries(payload.entries);
      })
      .catch(() => undefined);
  }, []);

  const visible = useMemo(() => {
    const needle = query.toLowerCase().trim();
    return entries.filter((entry) => {
      const status = statusFor(entry);
      return (filter === "all" || status === filter) &&
        (!needle || `${entry.id} ${entry.title} ${entry.family} ${entry.source ?? ""}`.toLowerCase().includes(needle));
    });
  }, [entries, filter, query]);

  const filterCounts = useMemo(() => {
    const counts: Record<"all" | Status, number> = {
      all: entries.length,
      verified: 0,
      formalization: 0,
      computation: 0,
      conjecture: 0,
      provisional: 0,
    };
    for (const entry of entries) counts[statusFor(entry)] += 1;
    return counts;
  }, [entries]);

  const chooseFilter = (value: "all" | Status) => {
    setFilter(value);
    setLimit(8);
  };

  return (
    <div className="tracker-card">
      <div className="tracker-controls">
        <div className="filter-list" aria-label="Filter theorem tracker">
          {filters.map((item) => (
            <button
              className={filter === item.value ? "active" : ""}
              key={item.value}
              onClick={() => chooseFilter(item.value)}
              aria-pressed={filter === item.value}
              type="button"
            >
              {item.label} · {filterCounts[item.value]}
            </button>
          ))}
        </div>
        <label className="search">
          <span className="sr-only">Search the theorem tracker</span>
          <span aria-hidden="true">⌕</span>
          <input
            value={query}
            onChange={(event) => { setQuery(event.target.value); setLimit(8); }}
            placeholder="Search statements"
          />
        </label>
      </div>
      <div className="tracker-table" role="table" aria-label="Homotopy theorem tracker">
        <div className="tracker-row tracker-head" role="row">
          <span role="columnheader">ID</span><span role="columnheader">Statement</span><span role="columnheader">Family</span><span role="columnheader">Knowledge status</span>
        </div>
        {visible.slice(0, limit).map((entry) => {
          const status = statusFor(entry);
          const sourceUrl = entry.source?.match(/https?:\/\/[^\s)]+/)?.[0];
          return (
            <div className="tracker-row" role="row" key={entry.id}>
              <span className="tracker-id" role="cell">{entry.id}</span>
              <span className="tracker-statement" role="cell">
                <a href={`https://github.com/Vilin97/homotopy-groups-lean/blob/main/manifests/problems/${entry.id}.toml`}><strong>{entry.title}</strong></a>
                {sourceUrl ? <a href={sourceUrl} title={entry.source ?? undefined}>Primary source ↗</a> : <small>{entry.knowledge_status}</small>}
              </span>
              <span role="cell">{entry.family}</span>
              <span role="cell"><i className={`status ${status}`}>{labelFor(entry)}</i></span>
            </div>
          );
        })}
        {visible.length === 0 && <div className="no-results">No statements match this view.</div>}
      </div>
      <div className="tracker-foot" aria-live="polite">
        <span>Showing {Math.min(limit, visible.length)} of {visible.length} matching · {entries.length} total</span>
        {limit < visible.length ? (
          <button type="button" onClick={() => setLimit((current) => current + 8)}>Show 8 more ↓</button>
        ) : (
          <a href="https://github.com/Vilin97/homotopy-groups-lean/tree/main/manifests/problems">Machine-readable inventory ↗</a>
        )}
      </div>
    </div>
  );
}
