from __future__ import annotations

import json
import pathlib
import subprocess
import sys
import tempfile
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "scripts"))

from audit_dependency_git import AuditError, audit_benchmark  # noqa: E402


class DependencyGitAuditTests(unittest.TestCase):
    def make_fixture(self, root: pathlib.Path) -> tuple[pathlib.Path, str]:
        package = root / ".lake" / "packages" / "demo"
        package.mkdir(parents=True)
        subprocess.run(["git", "init", "-q", str(package)], check=True)
        (package / "Demo.txt").write_text("trusted\n", encoding="utf-8")
        subprocess.run(["git", "-C", str(package), "add", "Demo.txt"], check=True)
        subprocess.run(
            [
                "git", "-C", str(package), "-c", "user.name=Benchmark",
                "-c", "user.email=benchmark@example.invalid", "commit", "-qm", "pin",
            ],
            check=True,
        )
        subprocess.run(
            [
                "git", "-C", str(package), "remote", "add", "origin",
                "https://github.com/example/demo.git",
            ],
            check=True,
        )
        revision = subprocess.run(
            ["git", "-C", str(package), "rev-parse", "HEAD"],
            capture_output=True,
            text=True,
            check=True,
        ).stdout.strip()
        manifest = {
            "version": "1.2.0",
            "packagesDir": ".lake/packages",
            "packages": [{
                "name": "demo",
                "type": "git",
                "url": "https://github.com/example/demo",
                "rev": revision,
            }],
        }
        (root / "lake-manifest.json").write_text(
            json.dumps(manifest) + "\n", encoding="utf-8"
        )
        return package, revision

    def test_accepts_exact_public_pinned_package(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = pathlib.Path(tmp)
            self.make_fixture(root)
            self.assertEqual(audit_benchmark(root, environ={}), 1)

    def test_rejects_auth_config_without_echoing_secret(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = pathlib.Path(tmp)
            package, _ = self.make_fixture(root)
            secret = "AUTHORIZATION: bearer never-print-this"
            subprocess.run(
                [
                    "git", "-C", str(package), "config",
                    "http.https://github.com/.extraheader", secret,
                ],
                check=True,
            )
            with self.assertRaises(AuditError) as raised:
                audit_benchmark(root, environ={})
            self.assertNotIn(secret, str(raised.exception))
            self.assertIn("extraheader", str(raised.exception))

    def test_rejects_credential_bearing_remote(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = pathlib.Path(tmp)
            package, _ = self.make_fixture(root)
            subprocess.run(
                [
                    "git", "-C", str(package), "remote", "set-url", "origin",
                    "https://token@example.com/example/demo",
                ],
                check=True,
            )
            with self.assertRaisesRegex(AuditError, "credential-free"):
                audit_benchmark(root, environ={})

    def test_rejects_revision_drift_and_sensitive_environment(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = pathlib.Path(tmp)
            self.make_fixture(root)
            with self.assertRaisesRegex(AuditError, "GITHUB_TOKEN"):
                audit_benchmark(root, environ={"GITHUB_TOKEN": "not-printed"})
            manifest_path = root / "lake-manifest.json"
            manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
            manifest["packages"][0]["rev"] = "0" * 40
            manifest_path.write_text(json.dumps(manifest), encoding="utf-8")
            with self.assertRaisesRegex(AuditError, "revision"):
                audit_benchmark(root, environ={})


if __name__ == "__main__":
    unittest.main()
