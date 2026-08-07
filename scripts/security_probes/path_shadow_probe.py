#!/usr/bin/env python3
"""Prove a submission cannot replace evaluator executables through Lake's PATH.

The hostile initializer plants executable lookalikes in `.lake/build/bin`, the
directory that `lake env` prepends to PATH.  A maintained proof must still pass
and none of the lookalikes may run.  This exercises the generated `lake test`
entry point, the outer systemd wrapper, and the patched comparator together.
"""

from __future__ import annotations

import argparse
from collections import deque
import os
import pathlib
import shlex
import shutil
import signal
import subprocess
import sys
import tempfile
import threading
import time
from typing import TextIO


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
# WorkspaceTest's systemd service has a 45-minute RuntimeMaxSec. Keep the outer
# watchdog beyond it so the service can report its stage and exit.  The trusted
# build below happens before this clock starts, so compilation cannot consume
# the five-minute reporting margin.
TRUSTED_PRIME_TIMEOUT_SECONDS = 10 * 60
OUTER_TIMEOUT_SECONDS = 50 * 60
TERMINATION_GRACE_SECONDS = 5
DIAGNOSTIC_LIMIT_CHARS = 64 * 1024

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
  -- `.lake` is writable, but a symlink from it must not make an external
  -- trusted target writable through landrun's path-based policy.
  try
    IO.FS.writeFile ".lake/external-write-probe/sentinel" "mutated\n"
    IO.FS.writeFile ".lake/symlink-target-write-succeeded" "unsafe\n"
  catch _ => pure ()
'''


class ProbeError(RuntimeError):
    pass


class _BoundedOutput:
    def __init__(self, limit: int) -> None:
        if limit <= 0:
            raise ValueError("diagnostic output limit must be positive")
        self._limit = limit
        self._chunks: deque[str] = deque()
        self._length = 0
        self._truncated = False
        self._lock = threading.Lock()

    def append(self, chunk: str) -> None:
        if not chunk:
            return
        with self._lock:
            self._chunks.append(chunk)
            self._length += len(chunk)
            while self._length > self._limit:
                excess = self._length - self._limit
                first = self._chunks[0]
                if len(first) <= excess:
                    self._chunks.popleft()
                    self._length -= len(first)
                else:
                    self._chunks[0] = first[excess:]
                    self._length -= excess
                self._truncated = True

    def render(self) -> str:
        with self._lock:
            body = "".join(self._chunks)
            truncated = self._truncated
        if not truncated:
            return body
        return (
            f"[command output truncated to the last {self._limit} characters]\n"
            f"{body}"
        )


def _pump_output(pipe: TextIO, capture: _BoundedOutput, stream: TextIO) -> None:
    stream_failed = False
    try:
        while chunk := pipe.read(4096):
            capture.append(chunk)
            if stream_failed:
                continue
            try:
                stream.write(chunk)
                stream.flush()
            except (OSError, ValueError):
                stream_failed = True
    except (OSError, ValueError) as exc:
        capture.append(f"\n[output reader stopped: {exc}]\n")
    finally:
        try:
            pipe.close()
        except (OSError, ValueError):
            pass


def _process_group_exists(process_group: int) -> bool:
    try:
        os.killpg(process_group, 0)
    except ProcessLookupError:
        return False
    except PermissionError:
        return True
    return True


def _terminate_process_group(
    process: subprocess.Popen[str], process_group: int, grace: float
) -> bool:
    """Terminate a command's whole session, returning whether SIGKILL was needed."""

    try:
        os.killpg(process_group, signal.SIGTERM)
    except ProcessLookupError:
        process.wait()
        return False

    deadline = time.monotonic() + grace
    while _process_group_exists(process_group) and time.monotonic() < deadline:
        process.poll()
        time.sleep(min(0.05, max(0.0, deadline - time.monotonic())))

    escalated = _process_group_exists(process_group)
    if escalated:
        try:
            os.killpg(process_group, signal.SIGKILL)
        except ProcessLookupError:
            escalated = False

    try:
        process.wait(timeout=max(1.0, grace))
    except subprocess.TimeoutExpired:
        process.kill()
        process.wait(timeout=1.0)
    return escalated


def _diagnostic_message(message: str, output: str) -> str:
    if not output:
        return f"{message}\n[no command output captured]"
    return f"{message}\n--- last command output ---\n{output.rstrip()}"


def run(
    command: list[str],
    workspace: pathlib.Path,
    *,
    timeout: float = OUTER_TIMEOUT_SECONDS,
    termination_grace: float = TERMINATION_GRACE_SECONDS,
    diagnostic_limit: int = DIAGNOSTIC_LIMIT_CHARS,
    output_stream: TextIO | None = None,
) -> subprocess.CompletedProcess[str]:
    if timeout <= 0:
        raise ValueError("command timeout must be positive")
    if termination_grace <= 0:
        raise ValueError("termination grace period must be positive")

    capture = _BoundedOutput(diagnostic_limit)
    stream = sys.stderr if output_stream is None else output_stream
    process = subprocess.Popen(
        command,
        cwd=workspace,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
        encoding="utf-8",
        errors="replace",
        bufsize=1,
        start_new_session=True,
    )
    assert process.stdout is not None
    process_group = process.pid
    reader = threading.Thread(
        target=_pump_output,
        args=(process.stdout, capture, stream),
        name="path-shadow-output",
        daemon=True,
    )
    reader.start()

    try:
        returncode = process.wait(timeout=timeout)
    except subprocess.TimeoutExpired as exc:
        escalated = _terminate_process_group(process, process_group, termination_grace)
        reader.join(timeout=max(1.0, termination_grace))
        cleanup = "SIGTERM then SIGKILL" if escalated else "SIGTERM"
        raise ProbeError(
            _diagnostic_message(
                f"command `{shlex.join(command)}` timed out after {timeout:g} seconds; "
                f"terminated process group {process_group} with {cleanup}",
                capture.render(),
            )
        ) from exc
    except BaseException:
        _terminate_process_group(process, process_group, termination_grace)
        reader.join(timeout=max(1.0, termination_grace))
        raise

    reader.join(timeout=max(1.0, termination_grace))
    if reader.is_alive():
        _terminate_process_group(process, process_group, termination_grace)
        reader.join(timeout=1.0)
        raise ProbeError(
            _diagnostic_message(
                f"command `{shlex.join(command)}` left an output-producing child running",
                capture.render(),
            )
        )
    return subprocess.CompletedProcess(command, returncode, capture.render(), "")


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
        external = pathlib.Path(tmp) / "trusted-external"
        external.mkdir(mode=0o777)
        external.chmod(0o777)
        sentinel = external / "sentinel"
        sentinel.write_text("trusted\n", encoding="utf-8")
        sentinel.chmod(0o666)
        (lake_dir / "external-write-probe").symlink_to(
            external.resolve(), target_is_directory=True
        )

        # These two roots import only benchmark-owned code. Build them before
        # installing the hostile Submission so `lake test`'s outer watchdog
        # measures the comparator smoke itself, while the inner 45-minute
        # systemd deadline remains authoritative for untrusted evaluation.
        try:
            primed = run(
                ["lake", "build", "Challenge", "workspace_test"],
                workspace,
                timeout=TRUSTED_PRIME_TIMEOUT_SECONDS,
            )
        except ProbeError as exc:
            raise ProbeError(f"trusted pre-service prime failed:\n{exc}") from exc
        if primed.returncode != 0:
            raise ProbeError(
                "trusted pre-service prime failed:\n"
                f"{primed.stdout}"
            )

        submission = workspace / "Submission.lean"
        maintained = (ROOT / "examples" / "submissions" / "pi1_circle" / "Submission.lean").read_text(
            encoding="utf-8"
        )
        submission.write_text(maintained + HOSTILE_INITIALIZER, encoding="utf-8")

        try:
            result = run(["lake", "test"], workspace)
        except ProbeError as exc:
            raise ProbeError(f"hostile comparator smoke failed:\n{exc}") from exc
        marker = workspace / ".lake" / "path-shadow-executed"
        if marker.exists():
            raise ProbeError("a workspace-owned executable was invoked")
        if sentinel.read_text(encoding="utf-8") != "trusted\n":
            raise ProbeError("landrun allowed a write through an external .lake symlink")
        if (lake_dir / "symlink-target-write-succeeded").exists():
            raise ProbeError("external symlink write unexpectedly succeeded")
        if result.returncode != 0:
            raise ProbeError(
                "maintained proof failed with path shadows present:\n"
                f"{result.stdout}"
            )

    print("path_shadow_probe: PASS")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (OSError, subprocess.SubprocessError, ProbeError) as exc:
        raise SystemExit(f"path_shadow_probe: FAIL: {exc}") from exc
