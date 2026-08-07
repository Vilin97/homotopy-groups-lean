#!/usr/bin/env python3
"""Generate tracker and leaderboard JSON from manifests, research, and results."""

from __future__ import annotations

import argparse
import json
import pathlib
import re
import sys
import tomllib

from benchmark_trust import (
    SITE_SCHEMA_VERSION,
    TrustError,
    current_problem_fingerprints,
    validate_stored_result,
)

ROOT = pathlib.Path(__file__).resolve().parent.parent
STATUS_RE = re.compile(r"\bknowledge_status=([^;\s]+)")


def load_tracker(
    root: pathlib.Path, current_results: list[dict[str, object]] | None = None,
) -> list[dict[str, object]]:
    if current_results is None:
        _, current_results, _ = load_results(root)
    accepted = {
        str(result["problem_id"])
        for result in current_results
        if result.get("outcome") == "accepted" and isinstance(result.get("problem_id"), str)
    }

    rows: list[dict[str, object]] = []
    for path in sorted((root / "manifests" / "problems").glob("*.toml")):
        with path.open("rb") as handle:
            manifest = tomllib.load(handle)
        notes = manifest.get("notes", "")
        match = STATUS_RE.search(notes)
        knowledge_status = match.group(1) if match else "unspecified"
        module = manifest["module"].removeprefix("HomotopyGroups.")
        rows.append(
            {
                "id": manifest["id"],
                "title": manifest["title"],
                "family": module,
                "knowledge_status": knowledge_status,
                "formalization_status": (
                    "comparator_verified" if manifest["id"] in accepted else
                    "maintained_test" if manifest.get("test") is True else
                    "open"
                ),
                "source": manifest.get("source"),
                "notes": notes,
                "holes": manifest["holes"],
            }
        )
    return rows


def load_results(
    root: pathlib.Path,
    fingerprints: dict[str, str] | None = None,
) -> tuple[list[dict[str, object]], list[dict[str, object]], list[dict[str, object]]]:
    if fingerprints is None:
        fingerprints = current_problem_fingerprints(root)
    raw_results: list[dict[str, object]] = []
    for path in sorted((root / "results").glob("*.json")):
        if path.name == "index.json":
            continue
        try:
            data = json.loads(path.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError) as exc:
            raise ValueError(f"invalid result file {path}: {exc}") from exc
        try:
            data = dict(validate_stored_result(data, filename=path.name))
        except TrustError as exc:
            raise ValueError(f"invalid result file {path}: {exc}") from exc
        data["result_file"] = path.name
        raw_results.append(data)

    current_results = [
        row
        for row in raw_results
        if row["problem_fingerprint"] == fingerprints.get(str(row["problem_id"]))
    ]
    eligible = [
        row for row in current_results
        if row.get("outcome") == "accepted" and row.get("score_eligible") is True
    ]
    eligible.sort(key=lambda row: (int(str(row["run_id"])), int(str(row["run_attempt"]))))
    first_for_problem: dict[str, str] = {}
    per_actor: dict[str, dict[str, object]] = {}
    for row in eligible:
        actor = str(row["actor"])
        problem = str(row["problem_id"])
        first_for_problem.setdefault(problem, actor)
        state = per_actor.setdefault(actor, {"actor": actor, "problems": set(), "models": set()})
        state["problems"].add(problem)  # type: ignore[union-attr]
        state["models"].add(str(row["model"]))  # type: ignore[union-attr]

    entries: list[dict[str, object]] = []
    for actor, state in per_actor.items():
        problems = sorted(state["problems"])  # type: ignore[arg-type]
        entries.append(
            {
                "actor": actor,
                "solved": len(problems),
                "firsts": sum(first_for_problem[problem] == actor for problem in problems),
                "problems": problems,
                "models": sorted(state["models"]),  # type: ignore[arg-type]
            }
        )
    entries.sort(key=lambda row: (-int(row["solved"]), -int(row["firsts"]), str(row["actor"]).lower()))
    for index, entry in enumerate(entries, start=1):
        entry["rank"] = index
    return raw_results, current_results, entries


def payloads(root: pathlib.Path) -> dict[pathlib.Path, object]:
    fingerprints = current_problem_fingerprints(root)
    raw_results, current_results, leaderboard = load_results(root, fingerprints)
    tracker = load_tracker(root, current_results)
    stable_registry = json.loads((root / "research" / "stable-stems.json").read_text(encoding="utf-8"))
    open_problem_registry = json.loads(
        (root / "research" / "open-problems.json").read_text(encoding="utf-8")
    )
    return {
        root / "website" / "public" / "data" / "tracker.json": {
            "schema_version": SITE_SCHEMA_VERSION,
            "problem_count": len(tracker),
            "entries": tracker,
        },
        root / "website" / "public" / "data" / "stable-stems.json": stable_registry,
        root / "website" / "public" / "data" / "open-problems.json": open_problem_registry,
        root / "website" / "public" / "data" / "leaderboard.json": {
            "schema_version": SITE_SCHEMA_VERSION,
            "accepted_eligible_results": sum(
                row.get("outcome") == "accepted" and row.get("score_eligible") is True
                for row in current_results
            ),
            "current_result_count": len(current_results),
            "archived_result_count": len(raw_results) - len(current_results),
            "entries": leaderboard,
        },
        root / "results" / "index.json": {
            "schema_version": SITE_SCHEMA_VERSION,
            "result_count": len(current_results),
            "archived_result_count": len(raw_results) - len(current_results),
            "results": [
                {
                    key: row.get(key)
                    for key in (
                        "result_file", "problem_id", "outcome", "actor", "model",
                        "problem_fingerprint", "benchmark_commit", "submission_commit",
                        "run_id", "run_attempt", "issue_number", "score_eligible",
                    )
                }
                for row in current_results
            ],
        },
    }


def render(value: object) -> str:
    return json.dumps(value, indent=2, sort_keys=True, ensure_ascii=False) + "\n"


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--root", type=pathlib.Path, default=ROOT)
    args = parser.parse_args(argv)
    root = args.root.resolve()
    try:
        outputs = payloads(root)
    except (OSError, ValueError, tomllib.TOMLDecodeError, json.JSONDecodeError) as exc:
        print(f"site-data generation failed: {exc}", file=sys.stderr)
        return 1
    stale: list[str] = []
    for path, value in outputs.items():
        expected = render(value)
        if args.check:
            try:
                actual = path.read_text(encoding="utf-8")
            except OSError:
                actual = ""
            if actual != expected:
                stale.append(str(path.relative_to(root)))
        else:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(expected, encoding="utf-8")
    if stale:
        print("stale generated site data: " + ", ".join(stale), file=sys.stderr)
        return 1
    print(f"site data {'current' if args.check else 'generated'} ({len(outputs)} files)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
