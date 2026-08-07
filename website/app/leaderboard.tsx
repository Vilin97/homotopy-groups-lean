"use client";

import { useEffect, useState } from "react";
import initialLeaderboard from "../public/data/leaderboard.json";

type Leader = {
  rank: number;
  actor: string;
  solved: number;
  firsts: number;
  models: string[];
  problems: string[];
};

const liveLeaderboardUrl =
  "https://raw.githubusercontent.com/Vilin97/homotopy-groups-lean/main/website/public/data/leaderboard.json";

export function Leaderboard() {
  const [entries, setEntries] = useState<Leader[]>(initialLeaderboard.entries as Leader[]);

  useEffect(() => {
    fetch(`${liveLeaderboardUrl}?v=${Date.now()}`, { cache: "no-store" })
      .then((response) => response.ok ? response.json() : Promise.reject(new Error("leaderboard fetch failed")))
      .then((payload: { entries?: Leader[] }) => {
        if (Array.isArray(payload.entries)) setEntries(payload.entries);
      })
      .catch(() => undefined);
  }, []);

  return (
    <div className="leaderboard-card">
      <div className="leaderboard-head"><span>Rank / contributor</span><span>Solved</span><span>Firsts</span></div>
      {entries.length === 0 ? (
        <div className="empty-state">
          <div className="empty-orbit">π</div>
          <div><strong>The first place is open.</strong><p>No external submission has passed the public evaluator yet.</p></div>
          <a className="button primary" href="https://github.com/Vilin97/homotopy-groups-lean/issues/new?template=submit.yml">Claim a theorem <span aria-hidden="true">↗</span></a>
        </div>
      ) : (
        <div className="leader-rows">
          {entries.map((entry) => (
            <div className="leader-row" key={entry.actor}>
              <div><span>{String(entry.rank).padStart(2, "0")}</span><strong>@{entry.actor}</strong><small>{entry.models.join(" · ")}</small></div>
              <strong>{entry.solved}</strong>
              <strong>{entry.firsts}</strong>
            </div>
          ))}
        </div>
      )}
    </div>
  );
}
