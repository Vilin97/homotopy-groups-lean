#!/usr/bin/env python3
# Adapted from leanprover/lean-eval at commit 53348531969dc984e02e3be0379a7282c664abd9.
# Modified for homotopy-groups-lean; see NOTICE and LICENSE.
"""
Audit GitHub Actions workflows for mutable selectors.

Hard-fails on:
  - `uses: <action>@main`, `@master`, `@develop`, `@latest`
  - `uses: <action>@v<N>` or `@v<N>.<M>` (loose major / minor selectors;
    tags are mutable and the action publisher can move them)
  - `go-version: stable` / `latest`
  - `node-version: latest`
  - `python-version` without a patch component (e.g. `3.11` is loose)
  - `go install <pkg>@<ref>` in run-blocks where <ref> is `main`,
    `master`, `latest`, or `v<N>.<M>(.X)` (tag, mutable)
  - `git checkout <ref>` in run-blocks where <ref> looks like a tag
    rather than a 40-char SHA
  - moving `runs-on: *-latest` runner labels
  - setup actions whose pinned implementations still fetch mutable tool
    manifests or installers at runtime
  - Mathlib cache reads that do not explicitly clear custom URL overrides and
    force the trusted `leanprover-community/mathlib4` `master` container
  - Lake updates that can trigger Mathlib's implicit, unconstrained cache hook
  - folded/quoted run scalars and dynamic shell forms that obscure those
    security-sensitive command tokens

Per-line opt-out via inline trailing comment:
  - `# pin-audit: exempt -- <reason>`

Allowlist via repo-level config (TOML) at .github/pin-audit-allowlist.toml,
not yet implemented (kept simple deliberately; revisit if needed).

The script's exit code is the number of policy violations (capped at 255).
Zero means the workflows are clean.

This is the audit step required by SECURITY.md > "Validations done at
submission time" > action_pin_audit.
"""

from __future__ import annotations

import argparse
import dataclasses
import pathlib
import re
import shlex
import sys
from typing import Iterable

REPO_ROOT = pathlib.Path(__file__).resolve().parent.parent
DEFAULT_WORKFLOWS_DIR = REPO_ROOT / ".github" / "workflows"

# A 40-char hex SHA. Anything else used as a ref is mutable.
SHA_RE = re.compile(r"^[0-9a-f]{40}$")

# Tokens we explicitly reject as refs (case-insensitive).
MUTABLE_REF_NAMES = {"main", "master", "develop", "trunk", "latest", "head"}

# These actions remain runtime-mutable even when their own Git ref is a SHA.
# Use the repository's digest-verified installers or the fixed runner image.
FORBIDDEN_RUNTIME_ACTIONS = {
    "actions/setup-go",
    "actions/setup-node",
    "actions/setup-python",
    "leanprover/lean-action",
}

EXEMPT_MARKER_RE = re.compile(r"#\s*pin-audit:\s*exempt\b")

# `uses: owner/repo@ref` or `uses: owner/repo/sub@ref`
USES_RE = re.compile(r"^(?P<indent>\s*)(?:-\s*)?uses:\s*(?P<spec>\S+)\s*(?:#.*)?$")

# `go install <pkg>@<ref>` inside a run-block. Conservative match.
GO_INSTALL_RE = re.compile(r"\bgo\s+install\s+(?P<pkg>\S+?)@(?P<ref>\S+)")

# `git checkout <ref>` and `git -C <dir> checkout <ref>` inside run-blocks.
GIT_CHECKOUT_RE = re.compile(
    r"\bgit(?:\s+-C\s+[^\s&;|]+)?\s+checkout\s+(?P<ref>[^\s&;|]+)"
)

# `<key>: <value>` for keys we audit (supports inline comments).
KV_RE = re.compile(
    r"^(?P<indent>\s*)(?P<key>go-version|node-version|python-version):\s*(?P<value>\S+)\s*(?:#.*)?$"
)
RUNS_ON_RE = re.compile(r"^\s*runs-on:\s*(?P<value>\S+)\s*(?:#.*)?$")
FOLDED_RUN_RE = re.compile(r"^\s*(?:-\s*)?run:\s*>")
QUOTED_RUN_RE = re.compile(r"^\s*(?:-\s*)?run:\s*['\"]")
NO_CACHE_ON_UPDATE_RE = re.compile(
    r"^\s*MATHLIB_NO_CACHE_ON_UPDATE:\s*['\"]?1['\"]?\s*(?:#.*)?$",
    re.MULTILINE,
)


@dataclasses.dataclass(frozen=True)
class Violation:
    file: pathlib.Path
    line_no: int
    line: str
    message: str

    def render(self, repo_root: pathlib.Path) -> str:
        try:
            rel = self.file.relative_to(repo_root)
        except ValueError:
            rel = self.file
        return f"{rel}:{self.line_no}: {self.message}\n    {self.line.rstrip()}"


def _is_loose_ref(ref: str) -> bool:
    """A ref is 'loose' (mutable) unless it's a 40-char hex SHA."""
    return not SHA_RE.fullmatch(ref)


def _classify_uses_ref(spec: str) -> str | None:
    """Return a violation message for a `uses:` spec, or None if it's pinned.

    `spec` is the value after `uses:`, e.g. `actions/checkout@v4` or
    `owner/repo/path@<sha>` or a local action path like `./.github/...`.
    """
    if spec.startswith("./") or spec.startswith("../"):
        # Local action; not a supply-chain risk.
        return None
    if "@" not in spec:
        return f"`uses: {spec}` has no @ref; treat as ambiguous and pin to a SHA."
    action, ref = spec.rsplit("@", 1)
    if action.lower() in FORBIDDEN_RUNTIME_ACTIONS:
        return (
            f"`uses: {action}@…` fetches mutable or unverified tool payloads at runtime; "
            "use a repository-owned digest-verified installer or the fixed runner image."
        )
    if SHA_RE.fullmatch(ref):
        return None
    if ref.lower() in MUTABLE_REF_NAMES:
        return f"`uses: {action}@{ref}` is a mutable branch selector; pin to a 40-char SHA."
    if re.fullmatch(r"v\d+(\.\d+){0,2}", ref):
        return f"`uses: {action}@{ref}` is a tag selector (mutable); pin to a 40-char SHA."
    return f"`uses: {action}@{ref}` is not a 40-char SHA; pin to one."


def _classify_kv(key: str, value: str) -> str | None:
    if key in ("go-version", "node-version"):
        if value.lower() in {"stable", "latest", "lts/*", "lts"}:
            return f"`{key}: {value}` is a moving target; pin to a concrete version."
        # X.Y.Z is fine; X.Y is borderline (we accept), X alone is too loose
        if not re.fullmatch(r"\d+(\.\d+){1,2}", value.strip("'\"")):
            return f"`{key}: {value}` is not a concrete X.Y[.Z] version."
        return None
    if key == "python-version":
        v = value.strip("'\"")
        if v.lower() == "latest":
            return f"`python-version: {value}` is a moving target."
        if not re.fullmatch(r"\d+\.\d+(\.\d+)?", v):
            return f"`python-version: {value}` is not a concrete X.Y or X.Y.Z."
        return None
    return None


def _classify_go_install(pkg: str, ref: str) -> str | None:
    if SHA_RE.fullmatch(ref):
        return None
    if ref.lower() in MUTABLE_REF_NAMES:
        return f"`go install {pkg}@{ref}` is a mutable branch selector; pin to a 40-char SHA."
    return f"`go install {pkg}@{ref}` is not a 40-char SHA; pin to one."


def _classify_git_checkout(ref: str) -> str | None:
    if SHA_RE.fullmatch(ref):
        return None
    return f"`git checkout {ref}` is not a 40-char SHA; workflow checkouts must be immutable."


def _logical_command_tokens(lines: list[str], index: int) -> list[str] | None:
    """Parse the backslash-continued shell command containing `lines[index]`."""

    start = index
    while start > 0 and lines[start - 1].rstrip().endswith("\\"):
        start -= 1
    end = index
    while end < len(lines) - 1 and lines[end].rstrip().endswith("\\"):
        end += 1
    # A shell removes a backslash-newline pair without inserting a byte. Keep
    # any whitespace before the backslash so both token-boundary continuations
    # (`cache \\` / `get`) and within-token continuations (`ca\\` / `che`) are
    # reconstructed faithfully after YAML's common indentation is removed.
    segments: list[str] = []
    for offset, line in enumerate(lines[start:end + 1]):
        segment = line.strip()
        if offset < end - start:
            segment = segment[:-1]
        segments.append(segment)
    command = "".join(segments)
    try:
        return shlex.split(command, posix=True)
    except ValueError:
        return None


SANITIZED_ENV_PREFIX = [
    "env",
    "-u", "MATHLIB_CACHE_GET_URL",
    "-u", "MATHLIB_CACHE_FROM",
    "-u", "MATHLIB_CACHE_REPO_SCOPE",
]
SAFE_CACHE_GET_TOKENS = SANITIZED_ENV_PREFIX + [
    "lake", "exe", "cache", "get",
    "--repo=leanprover-community/mathlib4",
    "--cache-from=master",
]
SAFE_LAKE_UPDATE_TOKENS = SANITIZED_ENV_PREFIX + [
    "MATHLIB_NO_CACHE_ON_UPDATE=1",
    "lake", "update",
]


def _logical_commands(lines: list[str]) -> Iterable[tuple[int, int, list[str] | None]]:
    """Yield each physical or backslash-continued command exactly once."""

    index = 0
    while index < len(lines):
        end = index
        while end < len(lines) - 1 and lines[end].rstrip().endswith("\\"):
            end += 1
        yield index, end, _logical_command_tokens(lines, index)
        index = end + 1


def _contains_token_sequence(tokens: list[str], sequence: list[str]) -> bool:
    width = len(sequence)
    return any(tokens[index:index + width] == sequence for index in range(len(tokens) - width + 1))


def _is_cache_read(tokens: list[str]) -> bool:
    # Start at `cache get`, rather than requiring a literal `lake`, so aliases
    # such as `$lake_cmd exe cache get` fail closed too.
    return _contains_token_sequence(tokens, ["cache", "get"])


def _is_lake_update(tokens: list[str]) -> bool:
    if _contains_token_sequence(tokens, ["lake", "update"]):
        return True
    return any(
        token == "update" and index > 0 and "$" in tokens[index - 1]
        for index, token in enumerate(tokens)
    )


SENSITIVE_ALIAS_VALUES = {"lake", "cache", "get", "update"}


def _assigns_sensitive_alias(tokens: list[str]) -> bool:
    """Reject shell indirection that would hide a protected invocation."""

    for token in tokens:
        if "=" not in token:
            continue
        name, value = token.split("=", 1)
        if re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", name) and (
            value in SENSITIVE_ALIAS_VALUES or value.endswith("/lake")
        ):
            return True
    return False


def _uses_shell_evaluator(tokens: list[str]) -> bool:
    if "eval" in tokens:
        return True
    return any(
        index + 1 < len(tokens)
        and pathlib.PurePosixPath(token).name in {"bash", "sh"}
        and tokens[index + 1] == "-c"
        for index, token in enumerate(tokens)
    )


def _audit_obscured_shell_policy(path: pathlib.Path, lines: list[str]) -> list[Violation]:
    """Reject syntax that prevents reliable inspection of protected commands."""

    violations: list[Violation] = []
    for start, end, tokens in _logical_commands(lines):
        if tokens is None:
            continue
        if any(EXEMPT_MARKER_RE.search(lines[index]) for index in range(start, end + 1)):
            continue
        source = "\n".join(lines[start:end + 1])
        if _assigns_sensitive_alias(tokens):
            violations.append(Violation(
                path,
                start + 1,
                lines[start],
                "shell aliases for Lake/cache command tokens obscure dependency operations; "
                "use literal commands.",
            ))
        if "$'" in source:
            violations.append(Violation(
                path,
                start + 1,
                lines[start],
                "Bash ANSI-C quoting obscures security-sensitive shell tokens; use plain tokens.",
            ))
        if _uses_shell_evaluator(tokens):
            violations.append(Violation(
                path,
                start + 1,
                lines[start],
                "`eval` and `sh`/`bash -c` obscure security-sensitive shell tokens; "
                "invoke commands directly.",
            ))
    return violations


def _audit_cache_get_policy(path: pathlib.Path, lines: list[str]) -> list[Violation]:
    """Require every workflow cache read to select Mathlib's trusted master container."""

    violations: list[Violation] = []
    for start, end, tokens in _logical_commands(lines):
        if tokens is None or not _is_cache_read(tokens):
            continue
        if any(EXEMPT_MARKER_RE.search(lines[index]) for index in range(start, end + 1)):
            continue
        if tokens != SAFE_CACHE_GET_TOKENS:
            violations.append(Violation(
                path,
                start + 1,
                lines[start],
                "Mathlib cache reads must exactly clear `MATHLIB_CACHE_GET_URL`, "
                "`MATHLIB_CACHE_FROM`, and `MATHLIB_CACHE_REPO_SCOPE`, then select only "
                "the canonical repository's master container.",
            ))
    return violations


def _audit_lake_update_policy(path: pathlib.Path, text: str, lines: list[str]) -> list[Violation]:
    """Ensure Mathlib's post-update cache hook cannot bypass the explicit read policy."""

    violations: list[Violation] = []
    commands = list(_logical_commands(lines))
    has_lake_update = any(
        tokens is not None and _is_lake_update(tokens)
        for _start, _end, tokens in commands
    )
    if has_lake_update and not NO_CACHE_ON_UPDATE_RE.search(text):
        violations.append(Violation(
            path,
            1,
            lines[0] if lines else "",
            "workflows that run `lake update` must set workflow-level "
            "`MATHLIB_NO_CACHE_ON_UPDATE: '1'`.",
        ))
    for start, end, tokens in commands:
        if tokens is None:
            continue
        exempt = any(EXEMPT_MARKER_RE.search(lines[index]) for index in range(start, end + 1))
        if not _is_lake_update(tokens) or exempt:
            continue
        if tokens != SAFE_LAKE_UPDATE_TOKENS:
            violations.append(Violation(
                path,
                start + 1,
                lines[start],
                "`lake update` must exactly clear cache-source/scope overrides and "
                "suppress Mathlib's implicit cache hook.",
            ))
    return violations


def audit_file(path: pathlib.Path) -> list[Violation]:
    violations: list[Violation] = []
    try:
        text = path.read_text(encoding="utf-8")
    except OSError as exc:
        return [Violation(path, 0, "", f"failed to read: {exc}")]
    lines = text.splitlines()
    for line_no, line in enumerate(lines, start=1):
        if EXEMPT_MARKER_RE.search(line):
            continue
        m = USES_RE.match(line)
        if m:
            msg = _classify_uses_ref(m.group("spec"))
            if msg:
                violations.append(Violation(path, line_no, line, msg))
            continue
        m = RUNS_ON_RE.match(line)
        if m:
            value = m.group("value").strip("'\"")
            if value.lower().endswith("-latest"):
                violations.append(Violation(
                    path,
                    line_no,
                    line,
                    f"`runs-on: {value}` is a moving runner alias; use a fixed OS label.",
                ))
            continue
        if FOLDED_RUN_RE.match(line):
            violations.append(Violation(
                path,
                line_no,
                line,
                "folded YAML `run: >` scalars obscure shell token boundaries; use a literal "
                "`run: |` block.",
            ))
            continue
        if QUOTED_RUN_RE.match(line):
            violations.append(Violation(
                path,
                line_no,
                line,
                "quoted inline `run:` scalars obscure shell token boundaries; use a literal "
                "`run: |` block or an unquoted simple command.",
            ))
            continue
        m = KV_RE.match(line)
        if m:
            msg = _classify_kv(m.group("key"), m.group("value"))
            if msg:
                violations.append(Violation(path, line_no, line, msg))
            continue
        for gm in GO_INSTALL_RE.finditer(line):
            msg = _classify_go_install(gm.group("pkg"), gm.group("ref"))
            if msg:
                violations.append(Violation(path, line_no, line, msg))
        for cm in GIT_CHECKOUT_RE.finditer(line):
            msg = _classify_git_checkout(cm.group("ref"))
            if msg:
                violations.append(Violation(path, line_no, line, msg))
    violations.extend(_audit_cache_get_policy(path, lines))
    violations.extend(_audit_lake_update_policy(path, text, lines))
    violations.extend(_audit_obscured_shell_policy(path, lines))
    return violations


def audit_dir(workflows_dir: pathlib.Path) -> list[Violation]:
    violations: list[Violation] = []
    for path in sorted(workflows_dir.glob("*.yml")) + sorted(workflows_dir.glob("*.yaml")):
        violations.extend(audit_file(path))
    return violations


def parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--workflows-dir",
        type=pathlib.Path,
        default=DEFAULT_WORKFLOWS_DIR,
        help="Directory of workflow YAML files to audit.",
    )
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    args = parse_args(argv)
    workflows_dir: pathlib.Path = args.workflows_dir
    if not workflows_dir.is_dir():
        print(f"workflows dir not found: {workflows_dir}", file=sys.stderr)
        return 2
    violations = audit_dir(workflows_dir)
    if not violations:
        print(f"action_pin_audit: clean ({workflows_dir})")
        return 0
    print(
        f"action_pin_audit: {len(violations)} violation(s) in {workflows_dir}",
        file=sys.stderr,
    )
    for v in violations:
        print(v.render(REPO_ROOT), file=sys.stderr)
    return min(len(violations), 255)


if __name__ == "__main__":
    raise SystemExit(main())
