from __future__ import annotations

import pathlib
import sys
import tempfile
import unittest
from unittest import mock

ROOT = pathlib.Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "scripts"))

from hardened_comparator import (  # noqa: E402
    HARDENING_ARGS,
    HardenedComparatorError,
    command,
    resolve_lean_toolchain,
    service_command,
    trusted_path,
)


class HardenedComparatorTests(unittest.TestCase):
    def test_wraps_complete_comparator_tree_in_af_unix_denial(self) -> None:
        workspace = ROOT / "generated" / "pi1_circle_mulEquiv_int"
        args = service_command(
            workspace,
            ["/opt/comparator", "/tmp/enforced.json"],
            path="/opt/bin:/usr/bin",
            home="/home/evaluator",
            extra_env={
                "COMPARATOR_LANDRUN": "/opt/landrun",
                "COMPARATOR_LEAN4EXPORT": "/opt/lean4export",
                "COMPARATOR_NANODA": "/opt/nanoda_bin",
                "COMPARATOR_LAKE": "/opt/lake",
                "COMPARATOR_LEAN": "/opt/lean",
                "COMPARATOR_GIT": "/opt/git",
            },
        )
        self.assertEqual(args[0], "systemd-run")
        self.assertIn("--property=RestrictAddressFamilies=~AF_UNIX", args)
        self.assertIn("--property=SystemCallFilter=~@network-io @aio", args)
        self.assertIn("--property=PrivateUsers=yes", args)
        self.assertIn("--property=KillMode=control-group", args)
        self.assertIn("--wait", args)
        self.assertIn("--pipe", args)
        self.assertIn("PATH=/opt/bin:/usr/bin", args)
        self.assertIn("HOME=/home/evaluator", args)
        self.assertIn("UV_USE_IO_URING=0", args)
        self.assertIn("/usr/bin/env", args)
        self.assertIn("-i", args)
        self.assertEqual(args[-2:], ["/opt/comparator", "/tmp/enforced.json"])

    def test_template_uses_absolute_lake_env_and_comparator_tools(self) -> None:
        template = (ROOT / "templates" / "WorkspaceTest.lean").read_text(encoding="utf-8")
        self.assertIn('lakeBin, "env", comparatorBin', template)
        self.assertIn('let (leanBin, lakeBin) ← resolveLeanToolchain', template)
        self.assertIn('primeTrustedChallenge lakeBin workspace', template)
        self.assertIn('args := #["build", "Challenge"]', template)
        self.assertIn('let home ← IO.FS.createTempDir', template)
        self.assertIn('s!"HOME={serviceHome}"', template)
        self.assertNotIn('s!"HOME={home}"', template)
        self.assertIn('"UV_USE_IO_URING=0"', template)
        for variable in ("COMPARATOR_LAKE", "COMPARATOR_LEAN", "COMPARATOR_GIT"):
            self.assertIn(variable, template)

    def test_template_requires_explicit_comparator_verdict(self) -> None:
        template = (ROOT / "templates" / "WorkspaceTest.lean").read_text(encoding="utf-8")
        self.assertIn('exitCode == 0 && status == "accepted"', template)
        self.assertIn('exitCode == 2 && status == "candidate_rejected"', template)
        self.assertNotIn("rejectionStages", template)
        self.assertIn("IO.setAccessRights enforcedPath", template)
        self.assertIn("IO.setAccessRights statusPath", template)

        patch = (ROOT / "patches" / "comparator-stage-status.patch").read_text(
            encoding="utf-8"
        )
        self.assertEqual(patch.count('writeStatus "candidate_rejected"'), 2)
        self.assertIn(
            '+    if solutionBuild == 1 then\n'
            '+      writeStatus "candidate_rejected"\n'
            '+      IO.eprintln "Candidate solution did not compile."\n'
            '+      return 2\n'
            '+    throw <| .userError',
            patch,
        )
        self.assertIn("+def main (args : List String) : IO UInt32", patch)
        self.assertIn('+    envOverride := #[', patch)
        self.assertIn('+("UV_USE_IO_URING",some"0")]', patch.replace(" ", ""))

    def test_resolves_real_toolchain_binaries_not_elan_proxy(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            prefix = pathlib.Path(tmp) / "toolchain"
            bin_dir = prefix / "bin"
            bin_dir.mkdir(parents=True)
            for name in ("lean", "lake"):
                executable = bin_dir / name
                executable.write_text("#!/bin/sh\n", encoding="utf-8")
                executable.chmod(0o755)
            completed = mock.Mock(returncode=0, stdout=str(prefix) + "\n")
            with mock.patch(
                "hardened_comparator.resolve_executable", return_value="/opt/elan/bin/lean"
            ), mock.patch("hardened_comparator.subprocess.run", return_value=completed):
                lean, lake = resolve_lean_toolchain(path="/opt/elan/bin", workspace=ROOT)
            self.assertEqual(pathlib.Path(lean), (bin_dir / "lean").resolve())
            self.assertEqual(pathlib.Path(lake), (bin_dir / "lake").resolve())

    def test_rejects_empty_path(self) -> None:
        with self.assertRaises(HardenedComparatorError):
            command(ROOT, path="", home="/home/evaluator")

    def test_hardening_contract_has_no_duplicate_properties(self) -> None:
        self.assertEqual(len(HARDENING_ARGS), len(set(HARDENING_ARGS)))
        template = (ROOT / "templates" / "WorkspaceTest.lean").read_text(encoding="utf-8")
        preflight = (ROOT / "EvalTools" / "CheckComparatorInstallation.lean").read_text(encoding="utf-8")
        for arg in HARDENING_ARGS:
            if arg.startswith("--property="):
                self.assertIn(arg, template)
                self.assertIn(arg, preflight)

    def test_removes_workspace_owned_path_entries(self) -> None:
        workspace = ROOT / "generated" / "pi1_circle_mulEquiv_int"
        dirty = f"{workspace}/.lake/build/bin:/usr/bin"
        self.assertEqual(trusted_path(workspace, dirty), "/usr/bin")


if __name__ == "__main__":
    unittest.main()
