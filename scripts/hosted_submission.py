#!/usr/bin/env python3
"""Fetch a public, commit-pinned Lean submission and overlay only proof files.

The command never executes source from the submitted repository. It accepts a
single benchmark id and copies only `Submission.lean` plus `.lean` files below
`Submission/` into a fresh copy of the benchmark-owned generated workspace.
"""

from __future__ import annotations

import argparse
import dataclasses
import json
import os
import pathlib
import re
import shutil
import subprocess
import sys
import tempfile
import urllib.error
import urllib.request
from collections.abc import Mapping

from benchmark_trust import (
    INTAKE_SCHEMA_VERSION,
    TrustError,
    current_problem_fingerprint,
    validate_copied_files,
)

SHA_RE = re.compile(r"^[0-9a-f]{40}$")
REPO_URL_RE = re.compile(
    r"^https://github\.com/(?P<owner>[A-Za-z0-9][A-Za-z0-9-]*)/"
    r"(?P<repo>[A-Za-z0-9._-]+?)(?:\.git)?/?$"
)
PROBLEM_RE = re.compile(r"^[A-Za-z0-9][A-Za-z0-9_-]*$")
MAX_TOTAL_BYTES = 2 * 1024 * 1024
MAX_FILE_BYTES = 512 * 1024
MAX_FILES = 128
MAX_REPOSITORY_KIB = 100 * 1024
GIT_COMMAND_TIMEOUT_SECONDS = 60


class IntakeError(Exception):
    """A user-facing intake or overlay error."""


@dataclasses.dataclass(frozen=True)
class Intake:
    problem_id: str
    repository_url: str
    commit_sha: str
    submission_path: str
    model: str


def issue_section(body: str, heading: str) -> str:
    match = re.search(
        rf"^###\s+{re.escape(heading)}\s*\n+(?P<value>.+?)(?=\n+###\s|\Z)",
        body,
        re.MULTILINE | re.DOTALL,
    )
    if match is None:
        raise IntakeError(f"Missing `{heading}` section. Use the submission Issue Form.")
    value = match.group("value").strip()
    if not value or value.startswith("_No response_"):
        raise IntakeError(f"`{heading}` must not be empty.")
    return value


def parse_issue_event(path: pathlib.Path) -> Intake:
    try:
        event = json.loads(path.read_text(encoding="utf-8"))
        body = event["issue"]["body"]
    except (OSError, json.JSONDecodeError, KeyError, TypeError) as exc:
        raise IntakeError(f"Invalid issue event: {exc}") from exc
    if not isinstance(body, str):
        raise IntakeError("Issue body is not text.")
    return validate_intake(
        problem_id=issue_section(body, "Problem ID"),
        repository_url=issue_section(body, "Public repository URL"),
        commit_sha=issue_section(body, "Commit SHA"),
        submission_path=issue_section(body, "Submission directory"),
        model=issue_section(body, "Model or prover"),
    )


def validate_intake(
    *, problem_id: str, repository_url: str, commit_sha: str,
    submission_path: str, model: str,
) -> Intake:
    problem_id = problem_id.strip()
    repository_url = repository_url.strip()
    commit_sha = commit_sha.strip().lower()
    submission_path = submission_path.strip()
    model = model.strip()
    if not PROBLEM_RE.fullmatch(problem_id):
        raise IntakeError("Problem ID contains unsupported characters.")
    if REPO_URL_RE.fullmatch(repository_url) is None:
        raise IntakeError("Repository URL must be an HTTPS github.com owner/repository URL.")
    if not SHA_RE.fullmatch(commit_sha):
        raise IntakeError("Commit SHA must be exactly 40 lowercase hexadecimal characters.")
    if not submission_path or submission_path == ".":
        submission_path = "."
    else:
        pure = pathlib.PurePosixPath(submission_path)
        if (
            pure.is_absolute()
            or pure.as_posix() != submission_path
            or ".." in pure.parts
            or any(part in {"", "."} for part in pure.parts)
        ):
            raise IntakeError("Submission directory must be a normalized relative path.")
    if not model or len(model) > 200 or "\n" in model or "\r" in model:
        raise IntakeError("Model or prover must be a single line of at most 200 characters.")
    return Intake(problem_id, repository_url, commit_sha, submission_path, model)


def _run(args: list[str], *, cwd: pathlib.Path | None = None) -> str:
    command_environment = os.environ.copy()
    # The API token is needed only by urllib. Public Git transport does not need
    # it, so do not pass it to any child process while inspecting a submission.
    command_environment.pop("GITHUB_TOKEN", None)
    command_environment["GIT_TERMINAL_PROMPT"] = "0"
    try:
        completed = subprocess.run(
            args,
            cwd=cwd,
            env=command_environment,
            text=True,
            capture_output=True,
            check=False,
            timeout=GIT_COMMAND_TIMEOUT_SECONDS,
        )
    except subprocess.TimeoutExpired as exc:
        raise IntakeError(
            f"Command timed out after {GIT_COMMAND_TIMEOUT_SECONDS}s: {' '.join(args[:3])}"
        ) from exc
    if completed.returncode != 0:
        details = (completed.stderr or completed.stdout).strip()
        raise IntakeError(f"Command failed: {' '.join(args[:3])}: {details}")
    return completed.stdout.strip()


def validate_public_repository_metadata(payload: object) -> None:
    if not isinstance(payload, dict) or payload.get("private") is not False:
        raise IntakeError("Only public GitHub repositories are accepted.")
    size_kib = payload.get("size")
    if isinstance(size_kib, bool) or not isinstance(size_kib, int) or size_kib < 0:
        raise IntakeError("GitHub did not provide a valid repository size.")
    if size_kib > MAX_REPOSITORY_KIB:
        raise IntakeError(
            f"Repository size is {size_kib} KiB; maximum is {MAX_REPOSITORY_KIB} KiB."
        )


def github_api_headers(environ: Mapping[str, str] | None = None) -> dict[str, str]:
    """Build authenticated GitHub API headers without logging the token."""

    environ = os.environ if environ is None else environ
    token = environ.get("GITHUB_TOKEN")
    if not isinstance(token, str) or not token:
        raise IntakeError("GITHUB_TOKEN is required for GitHub repository metadata checks.")
    if len(token) > 4096 or "\n" in token or "\r" in token:
        raise IntakeError("GITHUB_TOKEN has an invalid format.")
    return {
        "Accept": "application/vnd.github+json",
        "Authorization": f"Bearer {token}",
        "User-Agent": "homotopy-groups-lean-submission-intake",
        "X-GitHub-Api-Version": "2022-11-28",
    }


def assert_public_repository(
    url: str, *, environ: Mapping[str, str] | None = None,
) -> None:
    match = REPO_URL_RE.fullmatch(url)
    assert match is not None
    api = f"https://api.github.com/repos/{match.group('owner')}/{match.group('repo')}"
    request = urllib.request.Request(
        api,
        headers=github_api_headers(environ),
    )
    try:
        with urllib.request.urlopen(request, timeout=30) as response:
            payload = json.loads(response.read().decode("utf-8"))
    except (urllib.error.URLError, json.JSONDecodeError) as exc:
        raise IntakeError(f"Could not verify public repository: {exc}") from exc
    validate_public_repository_metadata(payload)


def clone_exact_commit(intake: Intake, destination: pathlib.Path) -> None:
    destination.mkdir(parents=True, exist_ok=False)
    _run(["git", "init", "--quiet"], cwd=destination)
    _run(["git", "remote", "add", "origin", intake.repository_url], cwd=destination)
    # Fetch the caller-specified immutable object only; no submitted branch or
    # workflow is checked out by name.
    _run(["git", "fetch", "--quiet", "--depth=1", "origin", intake.commit_sha], cwd=destination)
    resolved = _run(["git", "rev-parse", "FETCH_HEAD^{commit}"], cwd=destination)
    if resolved != intake.commit_sha:
        raise IntakeError(f"Fetched commit {resolved}, expected {intake.commit_sha}.")
    _run(["git", "checkout", "--quiet", "--detach", resolved], cwd=destination)


def _safe_regular_file(path: pathlib.Path, root: pathlib.Path) -> pathlib.Path:
    if path.is_symlink():
        raise IntakeError(f"Symlinks are not accepted: {path.relative_to(root)}")
    try:
        resolved = path.resolve(strict=True)
        resolved.relative_to(root.resolve(strict=True))
    except (OSError, ValueError) as exc:
        raise IntakeError(f"Submission path escapes its repository: {path}") from exc
    if not resolved.is_file():
        raise IntakeError(f"Expected a regular file: {path.relative_to(root)}")
    if resolved.stat().st_size > MAX_FILE_BYTES:
        raise IntakeError(f"Submission file exceeds {MAX_FILE_BYTES} bytes: {path.relative_to(root)}")
    return resolved


def collect_proof_files(repo: pathlib.Path, relative_dir: str) -> list[tuple[pathlib.Path, pathlib.PurePosixPath]]:
    source = repo
    if relative_dir != ".":
        for part in pathlib.PurePosixPath(relative_dir).parts:
            source /= part
            if source.is_symlink():
                raise IntakeError(f"Symlinks are not accepted in submission path: {relative_dir}")
    if source.is_symlink() or not source.is_dir():
        raise IntakeError(f"Submission directory does not exist as a regular directory: {relative_dir}")
    main = source / "Submission.lean"
    if not main.exists():
        raise IntakeError(f"No Submission.lean in submission directory `{relative_dir}`.")
    files: list[tuple[pathlib.Path, pathlib.PurePosixPath]] = [
        (_safe_regular_file(main, repo), pathlib.PurePosixPath("Submission.lean"))
    ]
    helpers = source / "Submission"
    if helpers.exists():
        if helpers.is_symlink() or not helpers.is_dir():
            raise IntakeError("Submission/ must be a regular directory, not a symlink.")
        for candidate in sorted(helpers.rglob("*")):
            if candidate.is_symlink():
                raise IntakeError(f"Symlinks are not accepted: {candidate.relative_to(repo)}")
            if candidate.is_dir():
                continue
            if candidate.suffix != ".lean":
                continue
            rel = candidate.relative_to(helpers)
            if ".." in rel.parts:
                raise IntakeError(f"Invalid helper path: {rel}")
            files.append((_safe_regular_file(candidate, repo), pathlib.PurePosixPath("Submission") / rel.as_posix()))
    if len(files) > MAX_FILES:
        raise IntakeError(f"Submission has {len(files)} Lean files; maximum is {MAX_FILES}.")
    total = sum(path.stat().st_size for path, _ in files)
    if total > MAX_TOTAL_BYTES:
        raise IntakeError(f"Submission proof sources total {total} bytes; maximum is {MAX_TOTAL_BYTES}.")
    return files


def validate_exact_submission(intake: Intake) -> list[str]:
    """Fetch and inspect the exact submitted tree without executing its code."""

    with tempfile.TemporaryDirectory(prefix="homotopy-submission-validation-") as temporary:
        source_repo = pathlib.Path(temporary) / "source"
        clone_exact_commit(intake, source_repo)
        copied = [
            relative.as_posix()
            for _, relative in collect_proof_files(source_repo, intake.submission_path)
        ]
    try:
        return validate_copied_files(copied)
    except TrustError as exc:
        raise IntakeError(f"Invalid proof-file selection: {exc}") from exc


def prepare_workspace(
    *, intake: Intake, benchmark_root: pathlib.Path, source_repo: pathlib.Path,
    workspaces_root: pathlib.Path,
) -> dict[str, object]:
    manifest = benchmark_root / "manifests" / "problems" / f"{intake.problem_id}.toml"
    pristine = benchmark_root / "generated" / intake.problem_id
    if not manifest.is_file():
        raise IntakeError(f"Unknown problem id: {intake.problem_id}")
    if not (pristine / "Challenge.lean").is_file() or not (pristine / "config.json").is_file():
        raise IntakeError(f"Pristine workspace is missing for {intake.problem_id}; benchmark CI must generate it first.")
    try:
        fingerprint = current_problem_fingerprint(benchmark_root, intake.problem_id)
    except TrustError as exc:
        raise IntakeError(f"Could not bind the trusted problem workspace: {exc}") from exc
    target = workspaces_root / intake.problem_id
    if target.exists():
        raise IntakeError(f"Target workspace already exists: {target}")
    shutil.copytree(pristine, target, symlinks=False, ignore=shutil.ignore_patterns(".lake", ".git", "build"))
    copied: list[str] = []
    for source, relative in collect_proof_files(source_repo, intake.submission_path):
        destination = target.joinpath(*relative.parts)
        destination.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(source, destination, follow_symlinks=False)
        copied.append(relative.as_posix())
    try:
        copied = validate_copied_files(copied)
    except TrustError as exc:
        raise IntakeError(f"Invalid proof-file overlay: {exc}") from exc
    return {
        "schema_version": INTAKE_SCHEMA_VERSION,
        "problem_id": intake.problem_id,
        "problem_fingerprint": fingerprint,
        "repository_url": intake.repository_url,
        "submission_commit": intake.commit_sha,
        "submission_path": intake.submission_path,
        "model": intake.model,
        "copied_files": copied,
    }


def _args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    source = parser.add_mutually_exclusive_group(required=True)
    source.add_argument("--event-path", type=pathlib.Path)
    source.add_argument("--problem-id")
    parser.add_argument("--repository-url")
    parser.add_argument("--commit-sha")
    parser.add_argument("--submission-path", default=".")
    parser.add_argument("--model", default="workflow-dispatch")
    parser.add_argument("--benchmark-root", type=pathlib.Path, required=True)
    parser.add_argument("--workspaces-root", type=pathlib.Path)
    parser.add_argument("--metadata-out", type=pathlib.Path)
    parser.add_argument(
        "--validate-only",
        action="store_true",
        help=(
            "Validate fields and metadata, then fetch and inspect the exact commit/path "
            "without executing submitted code."
        ),
    )
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    args = _args(argv)
    try:
        if args.event_path:
            intake = parse_issue_event(args.event_path)
        else:
            missing = [name for name in ("repository_url", "commit_sha") if getattr(args, name) is None]
            if missing:
                raise IntakeError(f"Missing dispatch arguments: {', '.join(missing)}")
            intake = validate_intake(
                problem_id=args.problem_id,
                repository_url=args.repository_url,
                commit_sha=args.commit_sha,
                submission_path=args.submission_path,
                model=args.model,
            )
        benchmark_root = args.benchmark_root.resolve(strict=True)
        if not (benchmark_root / "manifests" / "problems" / f"{intake.problem_id}.toml").is_file():
            raise IntakeError(f"Unknown problem id: {intake.problem_id}")
        assert_public_repository(intake.repository_url)
        if args.validate_only:
            validate_exact_submission(intake)
            return 0
        if args.workspaces_root is None or args.metadata_out is None:
            raise IntakeError("--workspaces-root and --metadata-out are required for an overlay.")
        args.workspaces_root.mkdir(parents=True, exist_ok=False)
        with tempfile.TemporaryDirectory(prefix="homotopy-submission-") as temporary:
            source_repo = pathlib.Path(temporary) / "source"
            clone_exact_commit(intake, source_repo)
            metadata = prepare_workspace(
                intake=intake,
                benchmark_root=benchmark_root,
                source_repo=source_repo,
                workspaces_root=args.workspaces_root.resolve(),
            )
        args.metadata_out.parent.mkdir(parents=True, exist_ok=True)
        args.metadata_out.write_text(json.dumps(metadata, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    except IntakeError as exc:
        print(f"submission intake failed: {exc}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
