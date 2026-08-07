#!/usr/bin/env python3
"""Shared trust primitives for benchmark-bound hosted results.

The problem fingerprint deliberately covers the pristine generated workspace,
not a Git commit.  A result therefore remains current across unrelated
benchmark commits, but stops counting as soon as its exact trusted challenge,
comparator configuration, or generated support files change.
"""

from __future__ import annotations

import dataclasses
import hashlib
import json
import os
import pathlib
import re
import tomllib
from collections.abc import Mapping, Sequence

INTAKE_SCHEMA_VERSION = 1
RESULT_SCHEMA_VERSION = 2
SITE_SCHEMA_VERSION = 2

PROBLEM_ID_RE = re.compile(r"^[A-Za-z0-9][A-Za-z0-9_-]*$")
SHA_RE = re.compile(r"^[0-9a-f]{40}$")
FINGERPRINT_RE = re.compile(r"^sha256:[0-9a-f]{64}$")
POSITIVE_DECIMAL_RE = re.compile(r"^[1-9][0-9]*$")
REPOSITORY_URL_RE = re.compile(
    r"^https://github\.com/[A-Za-z0-9][A-Za-z0-9-]*/"
    r"[A-Za-z0-9._-]+?(?:\.git)?/?$"
)
ACTOR_RE = re.compile(r"^[A-Za-z0-9][A-Za-z0-9-]*(?:\[bot\])?$")

MAX_COPIED_FILES = 128
MAX_ACTOR_LENGTH = 100
MAX_MODEL_LENGTH = 200

RESULT_OUTCOMES = frozenset({"accepted", "rejected", "infrastructure_error"})
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

# This is the complete evaluator identity written into every hosted result.
# Keeping it in one module prevents the producer and recorder from drifting.
EXPECTED_TOOLCHAIN: dict[str, str] = {
    "runner": "ubuntu-24.04",
    "lean": "v4.32.2",
    "lean_archive_sha256": "5f2069e6f5db73780f374ccb49ce8ea649aa20a0cebf0116816744c999ce72aa",
    "mathlib": "905b95818eb32af7874a58b427f50c1711a5e96c",
    "mathlib_cache_repo": "leanprover-community/mathlib4",
    "mathlib_cache_from": "master",
    "go": "1.25.12",
    "go_archive_sha256": "234828b7a89e0e303d2556310ee549fbcf253d28de937bac3da13d6294262ac1",
    "landrun": "5ed4a3db3a4ad930d577215c6b9abaa19df7f99f",
    "lean4export": "4e7915201d3f9f04470d9eae002fa695f7cdc589",
    "comparator": "07bc4ea40f2266dcb861820a2ec1fa3244ed307f",
    "comparator_terminator_patch_upstream": "9badaf470d8f724346d33738bd273efacd78df76",
    "comparator_terminator_patch_sha256": "a421770633877895de509d185a07bf04169a5c9becd73e595315ec95d40f326c",
    "comparator_absolute_tools_patch_sha256": "c9796ebf468991d07acc31f2f8e95cef53f61164f03a1ad2302c14f725e2000e",
    "comparator_stage_status_patch_sha256": "23a7fa6e34ebc79f2b71576db10f012a32bca85400ca7bf246a7337a3dab9ca2",
    "nanoda": "68d5ca9db226849b41a6fff59d796ff19d0a8840",
}

_FINGERPRINT_DOMAIN = b"homotopy-groups-lean/problem-fingerprint/v1\0"
_IGNORED_DIRECTORY_NAMES = {".lake", ".git", ".cache", "build", "__pycache__"}
_IGNORED_FILE_NAMES = {"lake-manifest.json", ".DS_Store"}
_IGNORED_FILE_SUFFIXES = {".olean", ".ilean", ".trace", ".tmp", ".pyc"}
_REQUIRED_WORKSPACE_FILES = {
    "README.md",
    "lean-toolchain",
    "lakefile.toml",
    "Challenge.lean",
    "Solution.lean",
    "Submission.lean",
    "Submission/Helpers.lean",
    "WorkspaceTest.lean",
    "config.json",
    "holes.json",
}


class TrustError(ValueError):
    """A benchmark or hosted-result value violates the trust contract."""


@dataclasses.dataclass(frozen=True)
class WorkflowContext:
    actor: str
    run_attempt: str
    issue_number: int | None
    score_eligible: bool


def _hash_part(state: "hashlib._Hash", value: bytes) -> None:
    state.update(len(value).to_bytes(8, byteorder="big", signed=False))
    state.update(value)


def _included_workspace_files(workspace: pathlib.Path) -> list[tuple[str, pathlib.Path]]:
    if not workspace.is_dir():
        raise TrustError(f"Generated workspace does not exist: {workspace}")
    files: list[tuple[str, pathlib.Path]] = []
    for path in workspace.rglob("*"):
        relative = path.relative_to(workspace)
        if any(part in _IGNORED_DIRECTORY_NAMES for part in relative.parts):
            continue
        if path.is_symlink():
            raise TrustError(f"Trusted generated workspace contains a symlink: {relative.as_posix()}")
        if path.is_dir():
            continue
        if path.name in _IGNORED_FILE_NAMES or path.suffix in _IGNORED_FILE_SUFFIXES:
            continue
        if not path.is_file():
            raise TrustError(f"Trusted generated workspace contains a non-file: {relative.as_posix()}")
        files.append((relative.as_posix(), path))
    files.sort(key=lambda item: item[0])
    present = {relative for relative, _ in files}
    missing = sorted(_REQUIRED_WORKSPACE_FILES - present)
    if missing:
        raise TrustError(f"Generated workspace is missing trusted file(s): {', '.join(missing)}")
    return files


def problem_fingerprint(workspace: pathlib.Path, problem_id: str | None = None) -> str:
    """Return the canonical content fingerprint of one pristine workspace."""

    workspace = workspace.resolve(strict=True)
    problem_id = workspace.name if problem_id is None else problem_id
    if not isinstance(problem_id, str) or PROBLEM_ID_RE.fullmatch(problem_id) is None:
        raise TrustError("Invalid problem id for fingerprinting.")
    state = hashlib.sha256()
    state.update(_FINGERPRINT_DOMAIN)
    _hash_part(state, problem_id.encode("utf-8"))
    for relative, path in _included_workspace_files(workspace):
        _hash_part(state, relative.encode("utf-8"))
        _hash_part(state, path.read_bytes())
    return "sha256:" + state.hexdigest()


def manifest_problem_ids(benchmark_root: pathlib.Path) -> set[str]:
    """Load the exact problem-id set from the benchmark manifest directory."""

    manifest_dir = benchmark_root / "manifests" / "problems"
    if not manifest_dir.is_dir():
        raise TrustError(f"Manifest directory does not exist: {manifest_dir}")
    ids: set[str] = set()
    for path in sorted(manifest_dir.glob("*.toml")):
        try:
            with path.open("rb") as handle:
                data = tomllib.load(handle)
        except (OSError, tomllib.TOMLDecodeError) as exc:
            raise TrustError(f"Invalid problem manifest {path}: {exc}") from exc
        problem_id = data.get("id")
        if not isinstance(problem_id, str) or PROBLEM_ID_RE.fullmatch(problem_id) is None:
            raise TrustError(f"Manifest {path} has an invalid problem id.")
        if path.stem != problem_id:
            raise TrustError(f"Manifest filename/id mismatch: {path.stem} != {problem_id}")
        if problem_id in ids:
            raise TrustError(f"Duplicate problem id in manifests: {problem_id}")
        ids.add(problem_id)
    return ids


def current_problem_fingerprint(benchmark_root: pathlib.Path, problem_id: str) -> str:
    if problem_id not in manifest_problem_ids(benchmark_root):
        raise TrustError(f"Unknown benchmark problem id: {problem_id}")
    return problem_fingerprint(benchmark_root / "generated" / problem_id, problem_id)


def current_problem_fingerprints(benchmark_root: pathlib.Path) -> dict[str, str]:
    ids = manifest_problem_ids(benchmark_root)
    return {
        problem_id: problem_fingerprint(benchmark_root / "generated" / problem_id, problem_id)
        for problem_id in sorted(ids)
    }


def validate_fingerprint(value: object) -> str:
    if not isinstance(value, str) or FINGERPRINT_RE.fullmatch(value) is None:
        raise TrustError("Invalid problem fingerprint.")
    return value


def validate_positive_decimal(value: object, field: str) -> str:
    if not isinstance(value, str) or POSITIVE_DECIMAL_RE.fullmatch(value) is None:
        raise TrustError(f"{field} must be a positive decimal string.")
    return value


def validate_actor(value: object) -> str:
    if (
        not isinstance(value, str)
        or len(value) > MAX_ACTOR_LENGTH
        or ACTOR_RE.fullmatch(value) is None
    ):
        raise TrustError("actor must be a valid single-line GitHub login.")
    return value


def validate_issue_number(value: object) -> int | None:
    if value is None:
        return None
    if isinstance(value, bool) or not isinstance(value, int) or value <= 0:
        raise TrustError("issue_number must be a positive integer or null.")
    return value


def validate_score_binding(issue_number: int | None, score_eligible: object) -> bool:
    if not isinstance(score_eligible, bool):
        raise TrustError("score_eligible must be boolean.")
    expected = issue_number is not None
    if score_eligible is not expected:
        raise TrustError("score_eligible must be true exactly for issue submissions.")
    return score_eligible


def validate_repository_url(value: object) -> str:
    if not isinstance(value, str) or REPOSITORY_URL_RE.fullmatch(value) is None:
        raise TrustError("repository_url must be an HTTPS GitHub repository root URL.")
    return value


def validate_submission_path(value: object) -> str:
    if not isinstance(value, str) or not value:
        raise TrustError("submission_path must be a nonempty string.")
    if value == ".":
        return value
    path = pathlib.PurePosixPath(value)
    if (
        path.is_absolute()
        or path.as_posix() != value
        or ".." in path.parts
        or any(part in {"", "."} for part in path.parts)
    ):
        raise TrustError("submission_path must be a normalized relative POSIX path.")
    return value


def validate_model(value: object) -> str:
    if (
        not isinstance(value, str)
        or not value
        or len(value) > MAX_MODEL_LENGTH
        or "\n" in value
        or "\r" in value
    ):
        raise TrustError("model must be one nonempty line of at most 200 characters.")
    return value


def validate_copied_files(value: object) -> list[str]:
    """Validate the exact proof-source path allowlist emitted by intake."""

    if not isinstance(value, list) or not value or len(value) > MAX_COPIED_FILES:
        raise TrustError("copied_files must be a nonempty bounded list.")
    if any(not isinstance(item, str) for item in value):
        raise TrustError("copied_files entries must be strings.")
    copied = list(value)
    if len(copied) != len(set(copied)):
        raise TrustError("copied_files must not contain duplicates.")
    if copied[0] != "Submission.lean":
        raise TrustError("copied_files must begin with Submission.lean.")
    helpers = copied[1:]
    if helpers != sorted(helpers):
        raise TrustError("Submission helper paths must be sorted.")
    for item in helpers:
        path = pathlib.PurePosixPath(item)
        if (
            path.is_absolute()
            or path.as_posix() != item
            or len(path.parts) < 2
            or path.parts[0] != "Submission"
            or ".." in path.parts
            or any(part in {"", "."} for part in path.parts)
            or path.suffix != ".lean"
        ):
            raise TrustError(f"copied_files contains a non-allowlisted path: {item}")
    return copied


def validate_exact_toolchain(value: object) -> dict[str, str]:
    if not isinstance(value, dict) or value != EXPECTED_TOOLCHAIN:
        raise TrustError("Result toolchain does not match the exact benchmark evaluator pins.")
    return dict(EXPECTED_TOOLCHAIN)


def workflow_context_from_environment(
    environ: Mapping[str, str] | None = None,
) -> WorkflowContext:
    """Recover trusted result expectations from standard GitHub runner state."""

    environ = os.environ if environ is None else environ
    try:
        actor = validate_actor(environ["GITHUB_ACTOR"])
        run_attempt = validate_positive_decimal(environ["GITHUB_RUN_ATTEMPT"], "run_attempt")
        event_name = environ["GITHUB_EVENT_NAME"]
    except KeyError as exc:
        raise TrustError(f"Missing trusted workflow environment variable: {exc.args[0]}") from exc
    if event_name == "workflow_dispatch":
        return WorkflowContext(actor, run_attempt, None, False)
    if event_name != "issues":
        raise TrustError(f"Unsupported result-recording event: {event_name}")
    try:
        event_path = pathlib.Path(environ["GITHUB_EVENT_PATH"])
        event = json.loads(event_path.read_text(encoding="utf-8"))
        issue_number = validate_issue_number(event["issue"]["number"])
    except (KeyError, OSError, json.JSONDecodeError, TypeError, TrustError) as exc:
        raise TrustError(f"Invalid trusted issue event payload: {exc}") from exc
    assert issue_number is not None
    return WorkflowContext(actor, run_attempt, issue_number, True)


def require_exact_fields(value: object, fields: Sequence[str], label: str) -> dict[str, object]:
    if not isinstance(value, dict):
        raise TrustError(f"{label} must be a JSON object.")
    expected = set(fields)
    actual = set(value)
    if actual != expected:
        raise TrustError(f"Unexpected {label} fields: {sorted(actual ^ expected)}")
    return value


def expected_result_filename(result: Mapping[str, object]) -> str:
    """Return the append-only filename bound to one validated result record."""

    issue = result["issue_number"] if result["issue_number"] is not None else "dispatch"
    return f"issue-{issue}-run-{result['run_id']}-attempt-{result['run_attempt']}.json"


def validate_stored_result(value: object, *, filename: str | None = None) -> dict[str, object]:
    """Validate the complete intrinsic contract of an append-only result.

    This intentionally does not require the result's problem fingerprint to be
    current: valid records become archived when a trusted workspace changes.
    Workflow-only facts are checked before recording; every fact retained in a
    stored record is checked again here before deriving public site data.
    """

    data = require_exact_fields(value, RESULT_FIELDS, "stored result")
    if data["schema_version"] != RESULT_SCHEMA_VERSION:
        raise TrustError("Unsupported stored result schema version.")
    problem_id = data["problem_id"]
    if not isinstance(problem_id, str) or PROBLEM_ID_RE.fullmatch(problem_id) is None:
        raise TrustError("Invalid stored result problem id.")
    validate_fingerprint(data["problem_fingerprint"])
    outcome = data["outcome"]
    if not isinstance(outcome, str) or outcome not in RESULT_OUTCOMES:
        raise TrustError("Invalid stored result outcome.")
    for field in ("benchmark_commit", "submission_commit"):
        value = data[field]
        if not isinstance(value, str) or SHA_RE.fullmatch(value) is None:
            raise TrustError(f"Invalid stored result {field}.")
    validate_repository_url(data["repository_url"])
    validate_submission_path(data["submission_path"])
    validate_model(data["model"])
    validate_actor(data["actor"])
    validate_positive_decimal(data["run_id"], "run_id")
    validate_positive_decimal(data["run_attempt"], "run_attempt")
    issue_number = validate_issue_number(data["issue_number"])
    validate_score_binding(issue_number, data["score_eligible"])
    validate_exact_toolchain(data["toolchain"])
    passed = outcome == "accepted"
    expected_checks = {"comparator": passed, "lean_kernel": passed, "nanoda": passed}
    if data["checks"] != expected_checks:
        raise TrustError("Stored kernel/comparator checks are inconsistent with outcome.")
    validate_copied_files(data["copied_files"])
    if filename is not None and filename != expected_result_filename(data):
        raise TrustError(
            f"Stored result filename does not match its workflow identity: {filename}"
        )
    return data


def result_matches_current_benchmark(
    result: Mapping[str, object], current_fingerprints: Mapping[str, str]
) -> bool:
    """Return true only for a complete valid result on the current workspace."""

    try:
        data = validate_stored_result(result)
    except TrustError:
        return False
    problem_id = data["problem_id"]
    assert isinstance(problem_id, str)
    return data["problem_fingerprint"] == current_fingerprints.get(problem_id)
