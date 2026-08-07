#!/usr/bin/env python3
"""Turn trusted intake metadata and evaluator JSON into a bounded result artifact."""

from __future__ import annotations

import argparse
import hashlib
import json
import pathlib
import sys

from benchmark_trust import (
    EXPECTED_TOOLCHAIN,
    INTAKE_SCHEMA_VERSION,
    PROBLEM_ID_RE,
    RESULT_SCHEMA_VERSION,
    SHA_RE,
    TrustError,
    require_exact_fields,
    validate_actor,
    validate_copied_files,
    validate_fingerprint,
    validate_issue_number,
    validate_model,
    validate_positive_decimal,
    validate_repository_url,
    validate_score_binding,
    validate_submission_path,
)

INTAKE_FIELDS = (
    "schema_version",
    "problem_id",
    "problem_fingerprint",
    "repository_url",
    "submission_commit",
    "submission_path",
    "model",
    "copied_files",
)


def parse_evaluator(path: pathlib.Path, problem_id: str, process_succeeded: bool) -> tuple[str, bool]:
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return "infrastructure_error", False
    problems = data.get("problems")
    if not isinstance(problems, list):
        return "infrastructure_error", False
    matches = [row for row in problems if isinstance(row, dict) and row.get("id") == problem_id]
    if len(matches) != 1 or not isinstance(matches[0].get("succeeded"), bool):
        return "infrastructure_error", False
    row = matches[0]
    passed = row["succeeded"] is True
    exit_code = row.get("exit_code")
    if passed:
        if process_succeeded and exit_code == 0:
            return "accepted", True
        return "infrastructure_error", False
    # The trusted workspace wrapper returns 2 only when the patched comparator
    # reached a candidate-controlled solution stage and exited normally with
    # its ordinary failure code. Signals, service/setup errors, timeouts, and
    # malformed evaluator output remain infrastructure failures.
    if process_succeeded and exit_code == 2:
        return "rejected", False
    return "infrastructure_error", False


def validate_intake_metadata(value: object) -> dict[str, object]:
    metadata = require_exact_fields(value, INTAKE_FIELDS, "trusted intake metadata")
    if metadata["schema_version"] != INTAKE_SCHEMA_VERSION:
        raise TrustError("Unsupported trusted intake metadata schema version.")
    problem_id = metadata["problem_id"]
    if not isinstance(problem_id, str) or PROBLEM_ID_RE.fullmatch(problem_id) is None:
        raise TrustError("Invalid problem id in trusted intake metadata.")
    validate_fingerprint(metadata["problem_fingerprint"])
    submission_commit = metadata["submission_commit"]
    if not isinstance(submission_commit, str) or SHA_RE.fullmatch(submission_commit) is None:
        raise TrustError("Invalid submission commit in trusted intake metadata.")
    validate_repository_url(metadata["repository_url"])
    validate_submission_path(metadata["submission_path"])
    validate_model(metadata["model"])
    validate_copied_files(metadata["copied_files"])
    return metadata


def build_result_payload(
    *, metadata: object, outcome: str, passed: bool, benchmark_commit: str,
    actor: str, run_id: str, run_attempt: str, issue_number: int | None,
    score_eligible: bool,
) -> dict[str, object]:
    metadata = validate_intake_metadata(metadata)
    if SHA_RE.fullmatch(benchmark_commit) is None:
        raise TrustError("Invalid benchmark commit.")
    actor = validate_actor(actor)
    run_id = validate_positive_decimal(run_id, "run_id")
    run_attempt = validate_positive_decimal(run_attempt, "run_attempt")
    issue_number = validate_issue_number(issue_number)
    score_eligible = validate_score_binding(issue_number, score_eligible)
    if outcome not in {"accepted", "rejected", "infrastructure_error"}:
        raise TrustError("Invalid evaluator outcome.")
    if not isinstance(passed, bool) or (outcome == "accepted") is not passed:
        raise TrustError("Evaluator outcome and kernel/comparator checks disagree.")
    return {
        "schema_version": RESULT_SCHEMA_VERSION,
        "problem_id": metadata["problem_id"],
        "problem_fingerprint": metadata["problem_fingerprint"],
        "outcome": outcome,
        "benchmark_commit": benchmark_commit,
        "submission_commit": metadata["submission_commit"],
        "repository_url": metadata["repository_url"],
        "submission_path": metadata["submission_path"],
        "model": metadata["model"],
        "actor": actor,
        "run_id": run_id,
        "run_attempt": run_attempt,
        "issue_number": issue_number,
        "score_eligible": score_eligible,
        "toolchain": dict(EXPECTED_TOOLCHAIN),
        "checks": {"comparator": passed, "lean_kernel": passed, "nanoda": passed},
        "copied_files": validate_copied_files(metadata["copied_files"]),
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--metadata", type=pathlib.Path, required=True)
    parser.add_argument("--evaluator-json", type=pathlib.Path, required=True)
    parser.add_argument("--process-outcome", choices=["success", "failure"], required=True)
    parser.add_argument("--benchmark-commit", required=True)
    parser.add_argument("--actor", required=True)
    parser.add_argument("--run-id", required=True)
    parser.add_argument("--run-attempt", required=True)
    parser.add_argument("--issue-number")
    parser.add_argument("--score-eligible", choices=["true", "false"], required=True)
    parser.add_argument("--output", type=pathlib.Path, required=True)
    parser.add_argument("--digest-output", type=pathlib.Path, required=True)
    args = parser.parse_args(argv)

    try:
        metadata = json.loads(args.metadata.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        raise SystemExit(f"invalid trusted intake metadata: {exc}") from exc
    try:
        metadata = validate_intake_metadata(metadata)
    except TrustError as exc:
        raise SystemExit(f"invalid trusted intake metadata: {exc}") from exc
    outcome, passed = parse_evaluator(
        args.evaluator_json,
        str(metadata["problem_id"]),
        args.process_outcome == "success",
    )
    issue_number = None
    if args.issue_number:
        if not args.issue_number.isdigit():
            raise SystemExit("invalid issue number")
        issue_number = int(args.issue_number)
    try:
        result = build_result_payload(
            metadata=metadata,
            outcome=outcome,
            passed=passed,
            benchmark_commit=args.benchmark_commit,
            actor=args.actor,
            run_id=args.run_id,
            run_attempt=args.run_attempt,
            issue_number=issue_number,
            score_eligible=args.score_eligible == "true",
        )
    except TrustError as exc:
        raise SystemExit(f"invalid hosted result: {exc}") from exc
    raw = (json.dumps(result, indent=2, sort_keys=True) + "\n").encode("utf-8")
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_bytes(raw)
    args.digest_output.write_text(hashlib.sha256(raw).hexdigest() + "\n", encoding="utf-8")
    print(outcome)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
