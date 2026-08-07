#!/usr/bin/env python3
"""Fail closed unless the outer evaluator sandbox enforces its contract."""

from __future__ import annotations

import os
import pathlib
import subprocess
import sys
import tempfile
import time

from hardened_comparator import service_command


class ProbeError(RuntimeError):
    pass


def run_payload(workspace: pathlib.Path, code: str, *, env: dict[str, str] | None = None) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        service_command(workspace, [sys.executable, "-c", code]),
        cwd=workspace,
        env=env,
        capture_output=True,
        text=True,
        check=False,
        timeout=30,
    )


def require_blocked(workspace: pathlib.Path, label: str, code: str) -> None:
    result = run_payload(workspace, code)
    if result.returncode == 0:
        raise ProbeError(f"outer sandbox allowed {label}")


def main() -> int:
    try:
        with tempfile.TemporaryDirectory(prefix="homotopy_systemd_probe_") as tmp:
            workspace = pathlib.Path(tmp)

            families = {
                "AF_UNIX socket": "import socket; socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)",
                "AF_INET TCP socket": "import socket; socket.socket(socket.AF_INET, socket.SOCK_STREAM)",
                "AF_INET UDP socket": "import socket; socket.socket(socket.AF_INET, socket.SOCK_DGRAM)",
            }
            for label, code in families.items():
                require_blocked(workspace, label, code)

            salted = os.environ.copy()
            salted["HOMOTOPY_EVALUATOR_SECRET_PROBE"] = "must-not-cross-service-boundary"
            cleaned = run_payload(
                workspace,
                "import os,sys; sys.exit(1 if 'HOMOTOPY_EVALUATOR_SECRET_PROBE' in os.environ else 0)",
                env=salted,
            )
            if cleaned.returncode != 0:
                raise ProbeError("parent environment crossed into evaluator service")

            sleeper_env = os.environ.copy()
            sleeper_env["HOMOTOPY_ANCESTOR_SECRET_PROBE"] = "must-not-be-readable"
            sleeper = subprocess.Popen(["/bin/sleep", "30"], env=sleeper_env)
            try:
                require_blocked(
                    workspace,
                    "same-user host /proc environ read",
                    f"open('/proc/{sleeper.pid}/environ', 'rb').read()",
                )
            finally:
                sleeper.terminate()
                sleeper.wait(timeout=5)

            heartbeat = workspace / "detached-heartbeat"
            child_code = (
                "import pathlib,time\n"
                f"p=pathlib.Path({str(heartbeat)!r})\n"
                "while True:\n"
                "    p.open('ab').write(b'x')\n"
                "    time.sleep(.05)\n"
            )
            launcher = (
                "import subprocess,sys,time; "
                f"subprocess.Popen([sys.executable,'-c',{child_code!r}], start_new_session=True); "
                "time.sleep(.25)"
            )
            detached = run_payload(workspace, launcher)
            if detached.returncode != 0 or not heartbeat.exists():
                raise ProbeError("could not exercise detached-child cleanup")
            size = heartbeat.stat().st_size
            time.sleep(.5)
            if heartbeat.stat().st_size != size:
                raise ProbeError("detached child survived evaluator service exit")

        print("systemd_sandbox_probe: network, environment, proc, and cgroup isolation enforced")
        return 0
    except (OSError, subprocess.SubprocessError, ProbeError) as exc:
        print(f"systemd_sandbox_probe failed: {exc}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
