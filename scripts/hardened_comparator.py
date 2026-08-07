#!/usr/bin/env python3
"""Construct the required systemd hardening wrapper for comparator.

Landrun cannot block AF_UNIX sockets on current Linux kernels. Comparator must
therefore run in a transient systemd unit whose address-family policy denies
AF_UNIX to comparator and every descendant, including untrusted elaboration.
"""

from __future__ import annotations

import os
import pathlib
import shutil
import subprocess


class HardenedComparatorError(RuntimeError):
    pass


HARDENING_ARGS = [
    "--user",
    "--pipe",
    "--wait",
    "--collect",
    "--quiet",
    "--property=RestrictAddressFamilies=~AF_UNIX",
    "--property=SystemCallArchitectures=native",
    "--property=SystemCallFilter=~@network-io @aio",
    "--property=PrivateUsers=yes",
    "--property=ProtectProc=invisible",
    "--property=ProcSubset=pid",
    "--property=NoNewPrivileges=yes",
    "--property=KillMode=control-group",
    "--property=MemoryMax=12G",
    "--property=TasksMax=512",
    "--property=LimitNOFILE=4096",
    "--property=LimitFSIZE=1G",
    "--property=RuntimeMaxSec=45min",
]


def service_command(
    workspace: pathlib.Path,
    payload: list[str],
    *,
    systemd_run: str = "systemd-run",
    path: str | None = None,
    home: str | None = None,
    extra_env: dict[str, str] | None = None,
) -> list[str]:
    executable_path = path if path is not None else os.environ.get("PATH", "")
    home_path = home if home is not None else os.environ.get("HOME", "")
    if not executable_path or not home_path:
        raise HardenedComparatorError(
            "PATH and HOME must be set; refusing to start the evaluator."
        )
    return [
        systemd_run,
        *HARDENING_ARGS,
        f"--working-directory={workspace.resolve()}",
        "--",
        "/usr/bin/env",
        "-i",
        f"PATH={executable_path}",
        f"HOME={home_path}",
        "LANG=C.UTF-8",
        "LC_ALL=C.UTF-8",
        "LEAN_ABORT_ON_PANIC=1",
        "UV_USE_IO_URING=0",
        *(f"{key}={value}" for key, value in sorted((extra_env or {}).items())),
        *payload,
    ]


def trusted_path(workspace: pathlib.Path, path: str) -> str:
    root = workspace.resolve()
    kept: list[str] = []
    for entry in path.split(os.pathsep):
        candidate = pathlib.Path(entry)
        if not candidate.is_absolute():
            continue
        try:
            candidate.resolve().relative_to(root)
        except ValueError:
            kept.append(str(candidate))
    return os.pathsep.join(kept)


def resolve_executable(name: str, *, path: str, workspace: pathlib.Path) -> str:
    resolved = shutil.which(name, path=path)
    if resolved is None:
        raise HardenedComparatorError(f"Could not resolve trusted executable: {name}")
    resolved_path = pathlib.Path(resolved).resolve()
    try:
        resolved_path.relative_to(workspace.resolve())
    except ValueError:
        return str(resolved_path)
    raise HardenedComparatorError(f"Refusing workspace-owned executable: {resolved_path}")


def resolve_lean_toolchain(*, path: str, workspace: pathlib.Path) -> tuple[str, str]:
    """Resolve real Lean/Lake binaries before entering the syscall filter.

    The `lean` found on PATH is commonly an elan proxy, which may probe the
    network and receive SIGSYS under the evaluator's network syscall denial.
    """
    launcher = resolve_executable("lean", path=path, workspace=workspace)
    result = subprocess.run(
        [launcher, "--print-prefix"],
        env={"PATH": path, "HOME": os.environ.get("HOME", "")},
        capture_output=True,
        text=True,
        timeout=30,
        check=False,
    )
    prefix = pathlib.Path(result.stdout.strip())
    if result.returncode != 0 or not prefix.is_absolute():
        raise HardenedComparatorError(
            "Could not resolve the active Lean toolchain prefix."
        )
    binaries: list[str] = []
    for name in ("lean", "lake"):
        candidate = (prefix / "bin" / name).resolve()
        if not candidate.is_file() or not os.access(candidate, os.X_OK):
            raise HardenedComparatorError(
                f"Lean toolchain executable does not exist: {candidate}"
            )
        try:
            candidate.relative_to(workspace.resolve())
        except ValueError:
            binaries.append(str(candidate))
            continue
        raise HardenedComparatorError(
            f"Refusing workspace-owned executable: {candidate}"
        )
    return binaries[0], binaries[1]


def command(
    workspace: pathlib.Path,
    *,
    comparator: str = "comparator",
    config: str = "config.json",
    path: str | None = None,
    home: str | None = None,
) -> list[str]:
    raw_path = path if path is not None else os.environ.get("PATH", "")
    safe_path = trusted_path(workspace, raw_path)
    comparator_bin = resolve_executable(comparator, path=safe_path, workspace=workspace)
    landrun_bin = resolve_executable("landrun", path=safe_path, workspace=workspace)
    lean4export_bin = resolve_executable("lean4export", path=safe_path, workspace=workspace)
    nanoda_bin = resolve_executable("nanoda_bin", path=safe_path, workspace=workspace)
    lean_bin, lake_bin = resolve_lean_toolchain(path=safe_path, workspace=workspace)
    git_bin = resolve_executable("git", path=safe_path, workspace=workspace)
    systemd_run_bin = resolve_executable(
        "systemd-run", path=safe_path, workspace=workspace
    )
    return service_command(
        workspace,
        [lake_bin, "env", comparator_bin, config],
        systemd_run=systemd_run_bin,
        path=safe_path,
        home=home,
        extra_env={
            "COMPARATOR_LANDRUN": landrun_bin,
            "COMPARATOR_LEAN4EXPORT": lean4export_bin,
            "COMPARATOR_NANODA": nanoda_bin,
            "COMPARATOR_LAKE": lake_bin,
            "COMPARATOR_LEAN": lean_bin,
            "COMPARATOR_GIT": git_bin,
        },
    )
