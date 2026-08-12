#!/usr/bin/env python3
"""Generate validated website JSON from manifests, research, and results."""

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
DEFAULT_LATTICE_DOMAIN = {"n_min": 1, "n_max": 92, "k_min": 0, "k_max": 108}
FORMALIZATION_STATUS_PRIORITY = {
    "lean_kernel_checked_local_source": 0,
    "dual_kernel_verified_reference": 1,
    "source_audited_imported_submission": 2,
    "source_audited_builds": 3,
    "source_audited_historical": 4,
}


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


def _required_string(row: dict[str, object], key: str, *, context: str) -> str:
    value = row.get(key)
    if not isinstance(value, str) or not value.strip():
        raise ValueError(f"{context}.{key} must be a non-empty string")
    return value


def _formalization_source_url(
    root: pathlib.Path,
    registry_path: pathlib.Path,
    row: dict[str, object],
) -> str:
    source = _required_string(row, "source", context=f"formalization {row.get('id')!r}")
    repository = _required_string(
        row, "repository", context=f"formalization {row.get('id')!r}"
    )
    if re.fullmatch(r"[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+", repository) is None:
        raise ValueError(
            f"formalization {row.get('id')!r}.repository must be GitHub owner/repo"
        )
    commit = _required_string(row, "commit", context=f"formalization {row.get('id')!r}")
    if re.fullmatch(r"[0-9a-f]{40}", commit) is None:
        raise ValueError(f"formalization {row.get('id')!r}.commit must be a full SHA")
    if source.startswith(("https://", "http://")):
        return source
    try:
        relative = (registry_path.parent / source).resolve().relative_to(root.resolve())
    except ValueError as exc:
        raise ValueError(
            f"formalization {row.get('id')!r}.source escapes the repository"
        ) from exc
    return f"https://github.com/{repository}/blob/{commit}/{relative.as_posix()}"


def _lattice_domain(root: pathlib.Path) -> dict[str, int]:
    coverage_path = root / "research" / "lattice-coverage.json"
    if not coverage_path.is_file():
        return dict(DEFAULT_LATTICE_DOMAIN)
    coverage = json.loads(coverage_path.read_text(encoding="utf-8"))
    raw_domain = coverage.get("domain") if isinstance(coverage, dict) else None
    if not isinstance(raw_domain, dict):
        raise ValueError("research/lattice-coverage.json.domain must be an object")
    domain: dict[str, int] = {}
    for key, fallback in DEFAULT_LATTICE_DOMAIN.items():
        value = raw_domain.get(key, fallback)
        if not isinstance(value, int):
            raise ValueError(f"research/lattice-coverage.json.domain.{key} must be an integer")
        domain[key] = value
    if domain["n_min"] > domain["n_max"] or domain["k_min"] > domain["k_max"]:
        raise ValueError("research/lattice-coverage.json has an inverted lattice domain")
    return domain


def load_formalization_inventory(root: pathlib.Path) -> dict[str, object]:
    """Validate and expand the audited formalization registry for the site.

    Human-readable coordinate descriptions stay in ``research/formalizations.json``;
    the adjacent ``cell_ranges`` are the machine-readable source of the lattice
    overlay.  The generated cells let the UI stay data-only when the audit grows.
    """

    registry_path = root / "research" / "formalizations.json"
    domain = _lattice_domain(root)
    empty = {
        "schema_version": "1.0.0",
        "reviewed_on": None,
        "source": (
            "https://github.com/Vilin97/homotopy-groups-lean/"
            "blob/main/research/formalizations.json"
        ),
        "records": [],
        "lattice": {**domain, "cell_count": 0, "cells": []},
    }
    # Unit-test benchmark fixtures intentionally omit the research audit.
    if not registry_path.is_file():
        return empty

    payload = json.loads(registry_path.read_text(encoding="utf-8"))
    if not isinstance(payload, dict):
        raise ValueError("research/formalizations.json must contain an object")
    raw_records = payload.get("formalizations")
    if not isinstance(raw_records, list):
        raise ValueError("research/formalizations.json.formalizations must be an array")

    records: list[dict[str, object]] = []
    record_by_id: dict[str, dict[str, object]] = {}
    records_for_cell: dict[tuple[int, int], list[str]] = {}
    for index, value in enumerate(raw_records):
        if not isinstance(value, dict):
            raise ValueError(f"formalizations[{index}] must be an object")
        row = value
        context = f"formalizations[{index}]"
        record_id = _required_string(row, "id", context=context)
        if record_id in record_by_id:
            raise ValueError(f"duplicate formalization id: {record_id}")
        system = _required_string(row, "system", context=context)
        result = _required_string(row, "result", context=context)
        model_relation = _required_string(row, "model_relation", context=context)
        status = _required_string(row, "status", context=context)
        source = _formalization_source_url(root, registry_path, row)
        declarations = row.get("declarations", [])
        if (
            not isinstance(declarations, list)
            or not all(isinstance(item, str) and item for item in declarations)
        ):
            raise ValueError(f"{context}.declarations must be an array of strings")

        overlay = row.get("lattice_overlay")
        coordinates: str | None = None
        lattice_kind: str | None = None
        cells: set[tuple[int, int]] = set()
        if overlay is not None:
            if not isinstance(overlay, dict):
                raise ValueError(f"{context}.lattice_overlay must be an object or null")
            coordinates = _required_string(
                overlay, "coordinates", context=f"{context}.lattice_overlay"
            )
            lattice_kind = _required_string(
                overlay, "kind", context=f"{context}.lattice_overlay"
            )
            ranges = overlay.get("cell_ranges")
            if not isinstance(ranges, list) or not ranges:
                raise ValueError(
                    f"{context}.lattice_overlay.cell_ranges must be a non-empty array"
                )
            for range_index, raw_range in enumerate(ranges):
                range_context = f"{context}.lattice_overlay.cell_ranges[{range_index}]"
                if not isinstance(raw_range, dict):
                    raise ValueError(f"{range_context} must be an object")
                bounds: dict[str, tuple[int, int]] = {}
                for axis in ("n", "k"):
                    raw_bounds = raw_range.get(axis)
                    if (
                        not isinstance(raw_bounds, list)
                        or len(raw_bounds) != 2
                        or not all(isinstance(item, int) for item in raw_bounds)
                    ):
                        raise ValueError(f"{range_context}.{axis} must be [min, max]")
                    lower, upper = raw_bounds
                    domain_lower = domain[f"{axis}_min"]
                    domain_upper = domain[f"{axis}_max"]
                    if lower > upper or lower < domain_lower or upper > domain_upper:
                        raise ValueError(
                            f"{range_context}.{axis} lies outside "
                            f"[{domain_lower}, {domain_upper}]"
                        )
                    bounds[axis] = (lower, upper)
                for n in range(bounds["n"][0], bounds["n"][1] + 1):
                    for k in range(bounds["k"][0], bounds["k"][1] + 1):
                        cell = (n, k)
                        if cell in cells:
                            raise ValueError(
                                f"{range_context} duplicates lattice cell n={n},k={k}"
                            )
                        cells.add(cell)

        record: dict[str, object] = {
            "id": record_id,
            "system": system,
            "result": result,
            "model_relation": model_relation,
            "status": status,
            "source": source,
            "declarations": declarations,
            "coordinates": coordinates,
            "lattice_kind": lattice_kind,
            "cell_count": len(cells),
            "note": row.get("note"),
        }
        records.append(record)
        record_by_id[record_id] = record
        for cell in sorted(cells):
            records_for_cell.setdefault(cell, []).append(record_id)

    def record_priority(record_id: str) -> tuple[int, int, str]:
        record = record_by_id[record_id]
        status = str(record["status"])
        system = str(record["system"])
        return (
            FORMALIZATION_STATUS_PRIORITY.get(status, 99),
            0 if system.startswith("Lean 4") else 1,
            record_id,
        )

    lattice_cells: list[dict[str, object]] = []
    for (n, k), record_ids in sorted(records_for_cell.items()):
        ordered_ids = sorted(record_ids, key=record_priority)
        lattice_cells.append(
            {"n": n, "k": k, "record_id": ordered_ids[0], "record_ids": ordered_ids}
        )

    reviewed_on = payload.get("reviewed_on")
    if not isinstance(reviewed_on, str) or not reviewed_on:
        raise ValueError("research/formalizations.json.reviewed_on must be a date string")
    return {
        "schema_version": payload.get("schema_version"),
        "reviewed_on": reviewed_on,
        "source": empty["source"],
        "records": records,
        "lattice": {**domain, "cell_count": len(lattice_cells), "cells": lattice_cells},
    }


def accepted_problem_catalog(
    current_results: list[dict[str, object]],
    tracker: list[dict[str, object]],
) -> list[dict[str, object]]:
    tracker_by_id = {str(row["id"]): row for row in tracker}
    grouped: dict[str, list[dict[str, object]]] = {}
    for row in current_results:
        if row.get("outcome") == "accepted":
            grouped.setdefault(str(row["problem_id"]), []).append(row)

    catalog: list[dict[str, object]] = []
    for problem_id, rows in grouped.items():
        rows.sort(key=lambda row: (int(str(row["run_id"])), int(str(row["run_attempt"]))))
        metadata = tracker_by_id.get(problem_id, {})
        eligible = [row for row in rows if row.get("score_eligible") is True]
        catalog.append(
            {
                "id": problem_id,
                "title": metadata.get("title", problem_id),
                "family": metadata.get("family", "Unknown"),
                "score_eligible": bool(eligible),
                "first_actor": str(eligible[0]["actor"]) if eligible else None,
                "actors": sorted({str(row["actor"]) for row in rows}),
                "models": sorted({str(row["model"]) for row in rows}),
                "result_count": len(rows),
                "result_files": [str(row["result_file"]) for row in rows],
            }
        )
    catalog.sort(key=lambda row: (not bool(row["score_eligible"]), str(row["title"])))
    return catalog


def payloads(root: pathlib.Path) -> dict[pathlib.Path, object]:
    fingerprints = current_problem_fingerprints(root)
    raw_results, current_results, leaderboard = load_results(root, fingerprints)
    tracker = load_tracker(root, current_results)
    accepted_problems = accepted_problem_catalog(current_results, tracker)
    formalization_inventory = load_formalization_inventory(root)
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
            "accepted_problems": accepted_problems,
            "formalization_inventory": formalization_inventory,
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
