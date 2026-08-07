#!/usr/bin/env python3
"""Fail closed unless every Lake Git package has safe, pinned identity.

Lake 4.32 uses each package's Git metadata when replaying build traces. Hosted
evaluation therefore retains that metadata outside the candidate-writable
workspace and audits it before untrusted Lean is elaborated.
"""

from __future__ import annotations

import argparse
import json
import os
import pathlib
import re
import subprocess
import tempfile
from urllib.parse import urlsplit


FULL_SHA = re.compile(r"[0-9a-f]{40}\Z")
PACKAGE_NAME = re.compile(r"[A-Za-z0-9_.-]+\Z")
GITHUB_PATH = re.compile(r"/[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+(?:\.git)?\Z")
SAFE_CORE_KEYS = {
    "core.bare",
    "core.filemode",
    "core.ignorecase",
    "core.logallrefupdates",
    "core.precomposeunicode",
    "core.repositoryformatversion",
    "core.symlinks",
}
SENSITIVE_ENV_EXACT = {
    "GH_TOKEN",
    "GITHUB_TOKEN",
    "GIT_ASKPASS",
    "GIT_CONFIG_COUNT",
    "GIT_PROXY_COMMAND",
    "GIT_SSH",
    "GIT_SSH_COMMAND",
    "SSH_ASKPASS",
}
SENSITIVE_ENV_PREFIXES = ("GIT_CONFIG_KEY_", "GIT_CONFIG_VALUE_")


class AuditError(RuntimeError):
    pass


def normalize_public_github_url(value: str) -> str:
    parsed = urlsplit(value)
    if (
        parsed.scheme != "https"
        or parsed.hostname != "github.com"
        or parsed.username is not None
        or parsed.password is not None
        or parsed.port is not None
        or parsed.query
        or parsed.fragment
        or not GITHUB_PATH.fullmatch(parsed.path)
    ):
        raise AuditError("dependency remote is not a credential-free public GitHub URL")
    return f"https://github.com{parsed.path.removesuffix('.git')}"


def audit_environment(environ: dict[str, str]) -> None:
    exposed = sorted(
        key
        for key in environ
        if key in SENSITIVE_ENV_EXACT or key.startswith(SENSITIVE_ENV_PREFIXES)
    )
    if exposed:
        raise AuditError(
            "credential-bearing Git environment variables are present: "
            + ", ".join(exposed)
        )


def _parse_config(raw: bytes, label: str) -> list[tuple[str, str]]:
    if len(raw) > 1024 * 1024:
        raise AuditError(f"Git config is unexpectedly large: {label}")
    entries: list[tuple[str, str]] = []
    for record in raw.split(b"\0"):
        if not record:
            continue
        key, separator, value = record.partition(b"\n")
        if not separator:
            raise AuditError(f"Git config has an invalid record: {label}")
        try:
            entries.append((key.decode("ascii").lower(), value.decode("utf-8")))
        except UnicodeDecodeError as exc:
            raise AuditError(f"Git config is not valid UTF-8/ASCII: {label}") from exc
    return entries


def read_config(path: pathlib.Path) -> list[tuple[str, str]]:
    if path.is_symlink() or not path.is_file():
        raise AuditError(f"Git config must be a regular non-symlink file: {path}")
    result = subprocess.run(
        ["git", "config", "--file", str(path), "--null", "--list"],
        stdout=subprocess.PIPE,
        stderr=subprocess.DEVNULL,
        timeout=10,
        check=False,
    )
    if result.returncode != 0:
        raise AuditError(f"Git rejected dependency config: {path}")
    return _parse_config(result.stdout, str(path))


def audit_config(entries: list[tuple[str, str]], expected_url: str, label: str) -> None:
    seen_origin: list[str] = []
    for key, value in entries:
        safe = key in SAFE_CORE_KEYS
        if key == "remote.origin.url":
            safe = True
            seen_origin.append(normalize_public_github_url(value))
        elif key == "remote.origin.fetch":
            safe = value == "+refs/heads/*:refs/remotes/origin/*"
        elif re.fullmatch(r"branch\.[A-Za-z0-9_.-]+\.remote", key):
            safe = value == "origin"
        elif re.fullmatch(r"branch\.[A-Za-z0-9_.-]+\.merge", key):
            safe = bool(re.fullmatch(r"refs/heads/[A-Za-z0-9_.-]+", value))
        if not safe:
            # Never include the value: a failure must not echo a credential.
            raise AuditError(f"unexpected Git config key or value in {label}: {key}")
    if seen_origin != [expected_url]:
        raise AuditError(f"dependency origin does not exactly match the manifest: {label}")


def _git_head(package: pathlib.Path) -> str:
    with tempfile.TemporaryDirectory(prefix="dependency-git-home-") as temporary_home:
        result = subprocess.run(
            ["git", "-C", str(package), "rev-parse", "HEAD"],
            env={
                "PATH": os.environ.get("PATH", ""),
                "HOME": temporary_home,
                "GIT_CONFIG_NOSYSTEM": "1",
                "GIT_TERMINAL_PROMPT": "0",
            },
            capture_output=True,
            text=True,
            timeout=10,
            check=False,
        )
    revision = result.stdout.strip()
    if result.returncode != 0 or not FULL_SHA.fullmatch(revision):
        raise AuditError(f"could not resolve dependency revision: {package}")
    return revision


def audit_benchmark(root: pathlib.Path, environ: dict[str, str] | None = None) -> int:
    root = root.resolve(strict=True)
    audit_environment(dict(os.environ if environ is None else environ))
    manifest_path = root / "lake-manifest.json"
    try:
        manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        raise AuditError(f"could not read Lake manifest: {manifest_path}") from exc
    if manifest.get("packagesDir") != ".lake/packages":
        raise AuditError("Lake manifest packagesDir must be exactly .lake/packages")
    packages = manifest.get("packages")
    if not isinstance(packages, list) or not packages:
        raise AuditError("Lake manifest must contain a non-empty package list")
    package_root = root / ".lake" / "packages"
    if package_root.is_symlink() or not package_root.is_dir():
        raise AuditError("hosted root package tree must be a regular directory")

    expected_names: set[str] = set()
    for entry in packages:
        if not isinstance(entry, dict):
            raise AuditError("Lake manifest package entry must be an object")
        name = entry.get("name")
        revision = entry.get("rev")
        url = entry.get("url")
        if (
            entry.get("type") != "git"
            or not isinstance(name, str)
            or not PACKAGE_NAME.fullmatch(name)
            or not isinstance(revision, str)
            or not FULL_SHA.fullmatch(revision)
            or not isinstance(url, str)
        ):
            raise AuditError("Lake manifest contains an invalid Git package identity")
        if name in expected_names:
            raise AuditError(f"duplicate Lake package name: {name}")
        expected_names.add(name)
        expected_url = normalize_public_github_url(url)
        package = package_root / name
        git_dir = package / ".git"
        if package.is_symlink() or not package.is_dir():
            raise AuditError(f"dependency package must be a regular directory: {name}")
        if git_dir.is_symlink() or not git_dir.is_dir():
            raise AuditError(f"dependency .git must be a regular directory: {name}")
        audit_config(read_config(git_dir / "config"), expected_url, name)
        if _git_head(package) != revision:
            raise AuditError(f"dependency revision does not match the manifest: {name}")

    actual_names = {
        child.name for child in package_root.iterdir() if child.is_dir() or child.is_symlink()
    }
    if actual_names != expected_names:
        raise AuditError("root package directory set does not exactly match the Lake manifest")
    return len(expected_names)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--benchmark-root", type=pathlib.Path, required=True)
    args = parser.parse_args(argv)
    try:
        count = audit_benchmark(args.benchmark_root)
    except (AuditError, OSError, subprocess.SubprocessError) as exc:
        raise SystemExit(f"dependency_git_audit: FAIL: {exc}") from exc
    print(f"dependency_git_audit: clean ({count} pinned public repositories)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
