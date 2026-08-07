#!/usr/bin/env python3
"""Prove a submission cannot replace evaluator executables through Lake's PATH.

The hostile initializer plants executable lookalikes in `.lake/build/bin`, the
directory that `lake env` prepends to PATH.  A maintained proof must still pass
and none of the lookalikes may run.  This exercises the generated `lake test`
entry point, the outer systemd wrapper, and the patched comparator together.
"""

from __future__ import annotations

import argparse
import pathlib
import shutil
import subprocess
import tempfile


ROOT = pathlib.Path(__file__).resolve().parents[2]
PROBLEM_ID = "pi1_circle_mulEquiv_int"
TOOLS = (
    "systemd-run",
    "lake",
    "lean",
    "git",
    "landrun",
    "lean4export",
    "nanoda_bin",
    "comparator",
)

HOSTILE_INITIALIZER = r'''

private def plantPathShadow (name : String) : IO Unit := do
  let cwd ← IO.currentDir
  let binDir := cwd / ".lake" / "build" / "bin"
  IO.FS.createDirAll binDir
  let executable := binDir / name
  IO.FS.writeFile executable "#!/bin/sh\n: > .lake/path-shadow-executed\nexit 77\n"
  IO.setAccessRights executable {
    user := { read := true, write := true, execution := true }
    group := { read := true, execution := true }
    other := { read := true, execution := true }
  }

initialize do
  for name in #["systemd-run", "lake", "lean", "git", "landrun",
      "lean4export", "nanoda_bin", "comparator"] do
    plantPathShadow name
'''


class ProbeError(RuntimeError):
    pass


def run(command: list[str], workspace: pathlib.Path, *, timeout: int = 1200) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        command,
        cwd=workspace,
        capture_output=True,
        text=True,
        check=False,
        timeout=timeout,
    )


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--require-tools",
        action="store_true",
        help="Fail instead of skipping when the pinned evaluator tools are absent.",
    )
    args = parser.parse_args(argv)

    missing = [tool for tool in TOOLS if shutil.which(tool) is None]
    if missing:
        message = f"path_shadow_probe: missing tools: {', '.join(missing)}"
        if args.require_tools:
            raise SystemExit(message)
        print(f"{message}; skipped")
        return 0

    with tempfile.TemporaryDirectory(prefix="homotopy_path_shadow_") as tmp:
        workspace = pathlib.Path(tmp) / PROBLEM_ID
        shutil.copytree(
            ROOT / "generated" / PROBLEM_ID,
            workspace,
            ignore=shutil.ignore_patterns(".lake"),
        )

        # CI and the VM have already primed the reviewed root dependency tree.
        # Reuse it read-only so this probe does not download a second Mathlib
        # cache merely to test executable resolution.
        trusted_packages = ROOT / ".lake" / "packages"
        if not trusted_packages.is_dir():
            raise ProbeError("trusted root dependencies are not primed")
        lake_dir = workspace / ".lake"
        lake_dir.mkdir()
        (lake_dir / "packages").symlink_to(trusted_packages.resolve(), target_is_directory=True)

        submission = workspace / "Submission.lean"
        maintained = (ROOT / "examples" / "submissions" / "pi1_circle" / "Submission.lean").read_text(
            encoding="utf-8"
        )
        submission.write_text(maintained + HOSTILE_INITIALIZER, encoding="utf-8")

        result = run(["lake", "test"], workspace)
        marker = workspace / ".lake" / "path-shadow-executed"
        if marker.exists():
            raise ProbeError("a workspace-owned executable was invoked")
        if result.returncode != 0:
            raise ProbeError(
                "maintained proof failed with path shadows present:\n"
                f"{result.stdout}\n{result.stderr}"
            )

    print("path_shadow_probe: PASS")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (OSError, subprocess.SubprocessError, ProbeError) as exc:
        raise SystemExit(f"path_shadow_probe: FAIL: {exc}") from exc
