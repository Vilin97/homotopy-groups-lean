#!/usr/bin/env python3
"""Validate an evaluator artifact and append one immutable result JSON file."""

from __future__ import annotations

import argparse
import hashlib
import json
import pathlib
import re
import sys

from benchmark_trust import (
    PROBLEM_ID_RE,
    RESULT_SCHEMA_VERSION,
    SHA_RE,
    TrustError,
    WorkflowContext,
    current_problem_fingerprint,
    require_exact_fields,
    validate_actor,
    validate_copied_files,
    validate_exact_toolchain,
    validate_fingerprint,
    validate_issue_number,
    validate_model,
    validate_positive_decimal,
    validate_repository_url,
    validate_score_binding,
    validate_submission_path,
    workflow_context_from_environment,
)

ROOT = pathlib.Path(__file__).resolve().parent.parent
OUTCOME = {"accepted", "rejected", "infrastructure_error"}
RESULT_FIELDS = (
    "schema_version",
    "problem_id",
    "problem_fingerprint",
    "outcome",
    "benchmark_commit",
    "submission_commit",
    "repository_url",
    "submission_path",
    "model",
    "actor",
    "run_id",
    "run_attempt",
    "issue_number",
    "score_eligible",
    "toolchain",
    "checks",
    "copied_files",
)


class ResultError(Exception):
    pass


def validate_result_payload(
    value: object,
    *,
    benchmark_root: pathlib.Path,
    expected_run_id: str,
    expected_benchmark_commit: str,
    workflow_context: WorkflowContext,
) -> dict[str, object]:
    try:
        data = require_exact_fields(value, RESULT_FIELDS, "result")
        if data["schema_version"] != RESULT_SCHEMA_VERSION:
            raise TrustError("Unsupported result schema version.")
        problem_id = data["problem_id"]
        if not isinstance(problem_id, str) or PROBLEM_ID_RE.fullmatch(problem_id) is None:
            raise TrustError("Invalid result problem id.")
        if data["outcome"] not in OUTCOME:
            raise TrustError("Invalid result outcome.")
        for key in ("benchmark_commit", "submission_commit"):
            if not isinstance(data[key], str) or SHA_RE.fullmatch(data[key]) is None:
                raise TrustError(f"Invalid {key}.")
        if data["benchmark_commit"] != expected_benchmark_commit:
            raise TrustError("Benchmark commit does not match the recording checkout.")
        run_id = validate_positive_decimal(data["run_id"], "run_id")
        expected_run_id = validate_positive_decimal(expected_run_id, "expected_run_id")
        if run_id != expected_run_id:
            raise TrustError("Run id does not match the workflow run.")
        run_attempt = validate_positive_decimal(data["run_attempt"], "run_attempt")
        expected_attempt = validate_positive_decimal(workflow_context.run_attempt, "expected_run_attempt")
        if run_attempt != expected_attempt:
            raise TrustError("Run attempt does not match the workflow attempt.")
        actor = validate_actor(data["actor"])
        if actor != validate_actor(workflow_context.actor):
            raise TrustError("Actor does not match the trusted workflow actor.")
        issue_number = validate_issue_number(data["issue_number"])
        if issue_number != validate_issue_number(workflow_context.issue_number):
            raise TrustError("Issue number does not match the trusted workflow event.")
        score_eligible = validate_score_binding(issue_number, data["score_eligible"])
        if score_eligible is not workflow_context.score_eligible:
            raise TrustError("Score eligibility does not match the trusted workflow event.")
        validate_repository_url(data["repository_url"])
        validate_submission_path(data["submission_path"])
        validate_model(data["model"])
        validate_exact_toolchain(data["toolchain"])
        passed = data["outcome"] == "accepted"
        expected_checks = {"comparator": passed, "lean_kernel": passed, "nanoda": passed}
        if data["checks"] != expected_checks:
            raise TrustError("Kernel/comparator checks are inconsistent with outcome.")
        validate_copied_files(data["copied_files"])
        artifact_fingerprint = validate_fingerprint(data["problem_fingerprint"])
        current_fingerprint = current_problem_fingerprint(benchmark_root, problem_id)
        if artifact_fingerprint != current_fingerprint:
            raise TrustError("Problem fingerprint does not match the current trusted workspace.")
    except TrustError as exc:
        raise ResultError(str(exc)) from exc
    return data


def verify_and_record(
    *, artifact: pathlib.Path, digest_file: pathlib.Path, output_dir: pathlib.Path,
    benchmark_root: pathlib.Path, expected_run_id: str, expected_benchmark_commit: str,
    workflow_context: WorkflowContext,
) -> pathlib.Path:
    raw = artifact.read_bytes()
    expected_digest = digest_file.read_text(encoding="utf-8").strip()
    actual_digest = hashlib.sha256(raw).hexdigest()
    if not re.fullmatch(r"[0-9a-f]{64}", expected_digest) or actual_digest != expected_digest:
        raise ResultError("Result artifact SHA-256 mismatch.")
    try:
        data = json.loads(raw)
    except json.JSONDecodeError as exc:
        raise ResultError(f"Invalid result JSON: {exc}") from exc
    data = validate_result_payload(
        data,
        benchmark_root=benchmark_root,
        expected_run_id=expected_run_id,
        expected_benchmark_commit=expected_benchmark_commit,
        workflow_context=workflow_context,
    )
    output_dir.mkdir(parents=True, exist_ok=True)
    issue = data["issue_number"] if data["issue_number"] is not None else "dispatch"
    name = f"issue-{issue}-run-{data['run_id']}-attempt-{data['run_attempt']}.json"
    destination = output_dir / name
    if destination.exists():
        raise ResultError(f"Refusing to overwrite existing result: {destination}")
    destination.write_bytes(raw if raw.endswith(b"\n") else raw + b"\n")
    return destination


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--artifact", type=pathlib.Path, required=True)
    parser.add_argument("--digest", type=pathlib.Path, required=True)
    parser.add_argument("--output-dir", type=pathlib.Path, required=True)
    parser.add_argument("--benchmark-root", type=pathlib.Path, default=ROOT)
    parser.add_argument("--expected-run-id", required=True)
    parser.add_argument("--expected-benchmark-commit", required=True)
    args = parser.parse_args(argv)
    try:
        workflow_context = workflow_context_from_environment()
        destination = verify_and_record(
            artifact=args.artifact,
            digest_file=args.digest,
            output_dir=args.output_dir,
            benchmark_root=args.benchmark_root.resolve(strict=True),
            expected_run_id=args.expected_run_id,
            expected_benchmark_commit=args.expected_benchmark_commit,
            workflow_context=workflow_context,
        )
    except (OSError, ResultError, TrustError) as exc:
        print(f"result recording failed: {exc}", file=sys.stderr)
        return 1
    print(destination)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
