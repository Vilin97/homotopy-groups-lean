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

    def audit_workflow(self, body: str) -> list[str]:
        with tempfile.TemporaryDirectory() as tmp:
            path = pathlib.Path(tmp) / "workflow.yml"
            path.write_text(body, encoding="utf-8")
            return [violation.message for violation in audit_file(path)]

    def test_finds_git_c_checkout_branch(self) -> None:
        self.assertTrue(self.audit_line("git -C dependency checkout release-branch"))

    def test_accepts_git_c_checkout_full_sha(self) -> None:
        self.assertEqual(
            self.audit_line("git -C dependency checkout " + "a" * 40),
            [],
        )

    def test_rejects_runtime_mutable_setup_action_even_at_sha(self) -> None:
        messages = self.audit_workflow(
            "jobs:\n  build:\n    steps:\n      - uses: actions/setup-python@" + "a" * 40 + "\n"
        )
        self.assertTrue(any("runtime" in message for message in messages))

    def test_rejects_case_variant_runtime_mutable_setup_action(self) -> None:
        messages = self.audit_workflow(
            "jobs:\n  build:\n    steps:\n      - uses: Actions/setup-python@" + "a" * 40 + "\n"
        )
        self.assertTrue(any("runtime" in message for message in messages))

    def test_rejects_moving_runner_alias(self) -> None:
        self.assertTrue(self.audit_workflow("jobs:\n  build:\n    runs-on: ubuntu-latest\n"))

    def test_accepts_fixed_runner_label(self) -> None:
        self.assertEqual(
            self.audit_workflow("jobs:\n  build:\n    runs-on: ubuntu-24.04\n"),
            [],
        )

    def test_accepts_sanitized_high_trust_mathlib_cache(self) -> None:
        workflow = """jobs:
  build:
    runs-on: ubuntu-24.04
    steps:
      - run: |
          env -u MATHLIB_CACHE_GET_URL -u MATHLIB_CACHE_FROM -u MATHLIB_CACHE_REPO_SCOPE \\
            lake exe cache get \\
              --repo=leanprover-community/mathlib4 \\
              --cache-from=master,legacy
"""
        self.assertEqual(self.audit_workflow(workflow), [])

    def test_rejects_unconstrained_mathlib_cache(self) -> None:
        messages = self.audit_workflow(
            "jobs:\n  build:\n    runs-on: ubuntu-24.04\n    steps:\n"
            "      - run: lake exe cache get\n"
        )
        self.assertTrue(any("Mathlib cache" in message for message in messages))

    def test_rejects_cache_read_that_inherits_repo_scope(self) -> None:
        workflow = """jobs:
  build:
    runs-on: ubuntu-24.04
    steps:
      - run: |
          env -u MATHLIB_CACHE_GET_URL -u MATHLIB_CACHE_FROM \\
            lake exe cache get \\
              --repo=leanprover-community/mathlib4 \\
              --cache-from=master,legacy
"""
        messages = self.audit_workflow(workflow)
        self.assertTrue(any("MATHLIB_CACHE_REPO_SCOPE" in message for message in messages))

    def test_rejects_cache_read_with_additional_source(self) -> None:
        workflow = """jobs:
  build:
    runs-on: ubuntu-24.04
    steps:
      - run: |
          env -u MATHLIB_CACHE_GET_URL -u MATHLIB_CACHE_FROM -u MATHLIB_CACHE_REPO_SCOPE \\
            lake exe cache get \\
              --repo=leanprover-community/mathlib4 \\
              --cache-from=master,legacy,forks
"""
        self.assertTrue(self.audit_workflow(workflow))

    def test_rejects_cache_read_without_legacy_mirror(self) -> None:
        workflow = """jobs:
  build:
    runs-on: ubuntu-24.04
    steps:
      - run: |
          env -u MATHLIB_CACHE_GET_URL -u MATHLIB_CACHE_FROM -u MATHLIB_CACHE_REPO_SCOPE \\
            lake exe cache get \\
              --repo=leanprover-community/mathlib4 \\
              --cache-from=master
"""
        self.assertTrue(self.audit_workflow(workflow))

    def test_rejects_cache_read_with_duplicate_source(self) -> None:
        workflow = """jobs:
  build:
    runs-on: ubuntu-24.04
    steps:
      - run: |
          env -u MATHLIB_CACHE_GET_URL -u MATHLIB_CACHE_FROM -u MATHLIB_CACHE_REPO_SCOPE \\
            lake exe cache get \\
              --repo=leanprover-community/mathlib4 \\
              --cache-from=master --cache-from=forks
"""
        self.assertTrue(self.audit_workflow(workflow))

    def test_rejects_backslash_split_cache_command(self) -> None:
        workflow = """jobs:
  build:
    runs-on: ubuntu-24.04
    steps:
      - run: |
          lake exe cache \\
            get --cache-from=forks
"""
        self.assertTrue(self.audit_workflow(workflow))

    def test_rejects_within_token_backslash_split_cache_command(self) -> None:
        workflow = """jobs:
  build:
    runs-on: ubuntu-24.04
    steps:
      - run: |
          lake exe ca\\
          che get --cache-from=forks
"""
        self.assertTrue(self.audit_workflow(workflow))

    def test_rejects_quoted_or_escaped_cache_command(self) -> None:
        for command in (
            '"lake" exe cache get --cache-from=forks',
            'la""ke exe cache get --cache-from=forks',
            r'lake exe ca\che get --cache-from=forks',
        ):
            with self.subTest(command=command):
                self.assertTrue(self.audit_line(command))

    def test_rejects_variable_lake_alias_for_cache_command(self) -> None:
        workflow = """jobs:
  build:
    runs-on: ubuntu-24.04
    steps:
      - run: |
          cache_cmd=lake
          "$cache_cmd" exe cache get --cache-from=forks
"""
        self.assertTrue(self.audit_workflow(workflow))

    def test_rejects_variable_cache_and_get_subcommands(self) -> None:
        for assignment, command in (
            ("subcommand=cache", 'lake exe "$subcommand" get --cache-from=forks'),
            ("operation=get", 'lake exe cache "$operation" --cache-from=forks'),
        ):
            with self.subTest(assignment=assignment):
                workflow = f"""jobs:
  build:
    runs-on: ubuntu-24.04
    steps:
      - run: |
          {assignment}
          {command}
"""
                self.assertTrue(self.audit_workflow(workflow))

    def test_rejects_variable_update_subcommand(self) -> None:
        workflow = """env:
  MATHLIB_NO_CACHE_ON_UPDATE: '1'
jobs:
  build:
    runs-on: ubuntu-24.04
    steps:
      - run: |
          operation=update
          lake "$operation"
"""
        self.assertTrue(self.audit_workflow(workflow))

    def test_rejects_ansi_c_quoted_cache_subcommand(self) -> None:
        self.assertTrue(self.audit_line(r"lake exe $'cache' get --cache-from=forks"))

    def test_rejects_shell_evaluators(self) -> None:
        for command in (
            "eval 'lake exe cache get --cache-from=forks'",
            "bash -c 'lake exe cache get --cache-from=forks'",
            "/bin/sh -c 'lake update'",
        ):
            with self.subTest(command=command):
                self.assertTrue(self.audit_line(command))

    def test_rejects_folded_run_scalar(self) -> None:
        for indicator in (">", ">2", ">-2", ">2-"):
            with self.subTest(indicator=indicator):
                workflow = f"""jobs:
  build:
    runs-on: ubuntu-24.04
    steps:
      - run: {indicator}
          lake exe cache
          get --cache-from=forks
"""
                self.assertTrue(
                    any("folded YAML" in message for message in self.audit_workflow(workflow))
                )

    def test_rejects_quoted_inline_run_scalar(self) -> None:
        for quote in ("'", '"'):
            with self.subTest(quote=quote):
                workflow = (
                    "jobs:\n  build:\n    runs-on: ubuntu-24.04\n    steps:\n"
                    f"      - run: {quote}lake exe cache get --cache-from=forks{quote}\n"
                )
                self.assertTrue(self.audit_workflow(workflow))

    def test_rejects_lake_update_without_cache_hook_suppression(self) -> None:
        messages = self.audit_workflow(
            "jobs:\n  build:\n    runs-on: ubuntu-24.04\n    steps:\n"
            "      - run: lake update\n"
        )
        self.assertTrue(any("post-update" in message or "implicit cache" in message for message in messages))

    def test_accepts_sanitized_lake_update(self) -> None:
        workflow = """env:
  MATHLIB_NO_CACHE_ON_UPDATE: '1'
jobs:
  build:
    runs-on: ubuntu-24.04
    steps:
      - run: |
          env -u MATHLIB_CACHE_GET_URL -u MATHLIB_CACHE_FROM -u MATHLIB_CACHE_REPO_SCOPE \\
            MATHLIB_NO_CACHE_ON_UPDATE=1 lake update
"""
        self.assertEqual(self.audit_workflow(workflow), [])

    def test_rejects_lookalike_cache_hook_suppression_value(self) -> None:
        workflow = """env:
  MATHLIB_NO_CACHE_ON_UPDATE: '1'
jobs:
  build:
    runs-on: ubuntu-24.04
    steps:
      - run: |
          env -u MATHLIB_CACHE_GET_URL -u MATHLIB_CACHE_FROM -u MATHLIB_CACHE_REPO_SCOPE \\
            MATHLIB_NO_CACHE_ON_UPDATE=10 lake update
"""
        self.assertTrue(self.audit_workflow(workflow))

    def test_rejects_backslash_split_or_quoted_lake_update(self) -> None:
        for command in (
            "lake " + "\\" + "\n            update",
            '"lake" update',
            'la""ke update',
        ):
            with self.subTest(command=command):
                workflow = """env:
  MATHLIB_NO_CACHE_ON_UPDATE: '1'
jobs:
  build:
    runs-on: ubuntu-24.04
    steps:
      - run: |
          env -u MATHLIB_CACHE_GET_URL -u MATHLIB_CACHE_FROM -u MATHLIB_CACHE_REPO_SCOPE \\
            MATHLIB_NO_CACHE_ON_UPDATE=10 """ + command + "\n"
                self.assertTrue(self.audit_workflow(workflow))

    def test_digest_pinned_installers_match_workflows(self) -> None:
        expected = {
            "install_pinned_lean.sh": (
                "lean-4.32.2-linux.tar.zst",
                "5f2069e6f5db73780f374ccb49ce8ea649aa20a0cebf0116816744c999ce72aa",
            ),
            "install_pinned_go.sh": (
                "go1.25.12.linux-amd64.tar.gz",
                "234828b7a89e0e303d2556310ee549fbcf253d28de937bac3da13d6294262ac1",
            ),
            "install_pinned_node.sh": (
                "node-v22.19.0-linux-x64.tar.xz",
                "c0649af18e6a24f6fe5535a3e86b341dd49a8e71117c8b68bde973ef834f16f2",
            ),
        }
        workflows = "\n".join(
            path.read_text(encoding="utf-8")
            for path in sorted((ROOT / ".github" / "workflows").glob("*.yml"))
        )
        for script_name, (archive_name, digest) in expected.items():
            script = (ROOT / "scripts" / script_name).read_text(encoding="utf-8")
            self.assertIn(archive_name, script)
            self.assertIn(digest, script)
            self.assertIn("--proto '=https'", script)
            self.assertIn("/usr/bin/sha256sum -c -", script)
            self.assertIn(f"bash scripts/{script_name}", workflows)
        go_installer = (ROOT / "scripts" / "install_pinned_go.sh").read_text(encoding="utf-8")
        self.assertIn("GOTOOLCHAIN=local", go_installer)

    def test_repository_workflows_pass_the_audit(self) -> None:
        for workflow in sorted((ROOT / ".github" / "workflows").glob("*.yml")):
            with self.subTest(workflow=workflow.name):
                self.assertEqual([v.message for v in audit_file(workflow)], [])


if __name__ == "__main__":
    unittest.main()
