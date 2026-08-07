from __future__ import annotations

import pathlib
import sys
import tempfile
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "scripts"))

from action_pin_audit import audit_file  # noqa: E402


class ActionPinAuditTests(unittest.TestCase):
    def audit_line(self, line: str) -> list[str]:
        with tempfile.TemporaryDirectory() as tmp:
            path = pathlib.Path(tmp) / "workflow.yml"
            path.write_text(f"jobs:\n  build:\n    steps:\n      - run: {line}\n", encoding="utf-8")
            return [violation.message for violation in audit_file(path)]

    def test_finds_git_c_checkout_branch(self) -> None:
        self.assertTrue(self.audit_line("git -C dependency checkout release-branch"))

    def test_accepts_git_c_checkout_full_sha(self) -> None:
        self.assertEqual(
            self.audit_line("git -C dependency checkout " + "a" * 40),
            [],
        )


if __name__ == "__main__":
    unittest.main()
