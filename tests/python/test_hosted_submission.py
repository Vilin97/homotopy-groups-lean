from __future__ import annotations

import hashlib
import copy
import json
import pathlib
import sys
import tempfile
import unittest
from unittest import mock

ROOT = pathlib.Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "scripts"))

import benchmark_trust as trust  # noqa: E402
import build_hosted_result as builder  # noqa: E402
import generate_site_data as site_data  # noqa: E402
import hosted_submission as hosted  # noqa: E402
import record_result as recorder  # noqa: E402


def make_benchmark(root: pathlib.Path, problem_id: str = "circle") -> str:
    manifest_dir = root / "manifests" / "problems"
    manifest_dir.mkdir(parents=True)
    (manifest_dir / f"{problem_id}.toml").write_text(
        "\n".join(
            [
                f'id = "{problem_id}"',
                'title = "Circle"',
                "test = false",
                'module = "HomotopyGroups.Spaces"',
                f'holes = ["{problem_id}"]',
                'submitter = "test"',
                'source = "https://example.com/source"',
                'notes = "knowledge_status=known_result/exact"',
                "",
            ]
        ),
        encoding="utf-8",
    )
    workspace = root / "generated" / problem_id
    (workspace / "Submission").mkdir(parents=True)
    files = {
        "README.md": f"# {problem_id}\n",
        "lean-toolchain": "leanprover/lean4:v4.32.2\n",
        "lakefile.toml": f'name = "{problem_id}"\n',
        "Challenge.lean": f"theorem {problem_id} : True := by sorry\n",
        "Solution.lean": f"theorem {problem_id} : True := by exact Submission.{problem_id}\n",
        "Submission.lean": f"theorem {problem_id} : True := by sorry\n",
        "Submission/Helpers.lean": "-- helper modules may be added here\n",
        "WorkspaceTest.lean": "def main : IO Unit := pure ()\n",
        "config.json": '{}\n',
        "holes.json": '{}\n',
    }
    for relative, contents in files.items():
        path = workspace / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(contents, encoding="utf-8")
    (root / "research").mkdir()
    (root / "research" / "stable-stems.json").write_text("{}\n", encoding="utf-8")
    (root / "research" / "open-problems.json").write_text("{}\n", encoding="utf-8")
    (root / "results").mkdir()
    return trust.current_problem_fingerprint(root, problem_id)


def intake_metadata(fingerprint: str, problem_id: str = "circle") -> dict[str, object]:
    return {
        "schema_version": trust.INTAKE_SCHEMA_VERSION,
        "problem_id": problem_id,
        "problem_fingerprint": fingerprint,
        "repository_url": "https://github.com/example/proofs",
        "submission_commit": "2" * 40,
        "submission_path": ".",
        "model": "human",
        "copied_files": ["Submission.lean", "Submission/Helper.lean"],
    }


def accepted_result(fingerprint: str, *, run_id: str = "123") -> dict[str, object]:
    return builder.build_result_payload(
        metadata=intake_metadata(fingerprint),
        outcome="accepted",
        passed=True,
        benchmark_commit="1" * 40,
        actor="alice",
        run_id=run_id,
        run_attempt="1",
        issue_number=7,
        score_eligible=True,
    )


def write_formalization_registry(
    root: pathlib.Path,
    cell_ranges: object,
) -> None:
    payload = {
        "schema_version": "1.0.0",
        "reviewed_on": "2026-08-08",
        "formalizations": [
            {
                "id": "test-circle",
                "system": "Lean 4",
                "repository": "example/formalization",
                "commit": "a" * 40,
                "declarations": ["Example.circle"],
                "result": "pi_1(Circle) is infinite cyclic",
                "model_relation": "test model",
                "status": "source_audited_builds",
                "source": "https://github.com/example/formalization/blob/" + "a" * 40 + "/Circle.lean",
                "lattice_overlay": {
                    "coordinates": "n=1,k=0",
                    "kind": "lean4_alternate_model",
                    "cell_ranges": cell_ranges,
                },
            }
        ],
    }
    (root / "research" / "formalizations.json").write_text(
        json.dumps(payload), encoding="utf-8"
    )


class IntakeTests(unittest.TestCase):
    def test_issue_form_round_trip(self) -> None:
        body = """### Problem ID

pi1_circle_mulEquiv_int

### Public repository URL

https://github.com/example/proofs

### Commit SHA

0123456789abcdef0123456789abcdef01234567

### Submission directory

examples/circle

### Model or prover

human + Lean
"""
        with tempfile.TemporaryDirectory() as tmp:
            event = pathlib.Path(tmp) / "event.json"
            event.write_text(json.dumps({"issue": {"body": body}}), encoding="utf-8")
            parsed = hosted.parse_issue_event(event)
        self.assertEqual(parsed.problem_id, "pi1_circle_mulEquiv_int")
        self.assertEqual(parsed.submission_path, "examples/circle")

    def test_path_traversal_rejected(self) -> None:
        for submission_path in ("../trusted", "/trusted", "proof/"):
            with self.subTest(submission_path=submission_path):
                with self.assertRaises(hosted.IntakeError):
                    hosted.validate_intake(
                        problem_id="p",
                        repository_url="https://github.com/example/proofs",
                        commit_sha="0" * 40,
                        submission_path=submission_path,
                        model="human",
                    )

    def test_collects_only_lean_proof_files_and_rejects_symlink(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            repo = pathlib.Path(tmp)
            source = repo / "proof"
            (source / "Submission").mkdir(parents=True)
            (source / "Submission.lean").write_text("import Submission.Helper\n", encoding="utf-8")
            (source / "Submission" / "Helper.lean").write_text("theorem ok : True := trivial\n", encoding="utf-8")
            (source / "lakefile.toml").write_text("malicious = true\n", encoding="utf-8")
            files = hosted.collect_proof_files(repo, "proof")
            self.assertEqual([relative.as_posix() for _, relative in files], ["Submission.lean", "Submission/Helper.lean"])
            (source / "Submission" / "Escape.lean").symlink_to(repo / "outside.lean")
            with self.assertRaises(hosted.IntakeError):
                hosted.collect_proof_files(repo, "proof")

    def test_git_subprocess_has_a_hard_timeout(self) -> None:
        inherited = {
            "GITHUB_TOKEN": "never-pass-to-git",
            "GIT_CONFIG_COUNT": "1",
            "GIT_CONFIG_KEY_0": "filter.evil.smudge",
            "GIT_CONFIG_VALUE_0": "run-attacker-code",
            "GIT_SSH_COMMAND": "run-attacker-code",
        }
        with mock.patch.dict(hosted.os.environ, inherited):
            with mock.patch.object(
                hosted.subprocess,
                "run",
                side_effect=hosted.subprocess.TimeoutExpired(["git", "fetch"], 60),
            ) as run:
                with self.assertRaisesRegex(hosted.IntakeError, "timed out"):
                    hosted._run(["git", "fetch", "origin"])
        self.assertEqual(run.call_args.kwargs["timeout"], hosted.GIT_COMMAND_TIMEOUT_SECONDS)
        child_env = run.call_args.kwargs["env"]
        self.assertNotIn("GITHUB_TOKEN", child_env)
        self.assertNotIn("GIT_CONFIG_COUNT", child_env)
        self.assertNotIn("GIT_CONFIG_KEY_0", child_env)
        self.assertNotIn("GIT_CONFIG_VALUE_0", child_env)
        self.assertNotIn("GIT_SSH_COMMAND", child_env)
        self.assertEqual(child_env["GIT_TERMINAL_PROMPT"], "0")
        self.assertEqual(child_env["GIT_ASKPASS"], "/bin/false")
        self.assertEqual(child_env["GIT_CONFIG_NOSYSTEM"], "1")
        self.assertEqual(child_env["GIT_CONFIG_GLOBAL"], "/dev/null")
        self.assertEqual(child_env["GIT_ATTR_NOSYSTEM"], "1")
        self.assertEqual(child_env["GIT_LFS_SKIP_SMUDGE"], "1")

    def test_github_metadata_request_is_authenticated_without_echoing_token(self) -> None:
        token = "ghs_top-secret-test-token"

        class Response:
            def __enter__(self) -> "Response":
                return self

            def __exit__(self, *_args: object) -> None:
                return None

            def read(self) -> bytes:
                return json.dumps({"private": False, "size": 1}).encode()

        with mock.patch.object(hosted.urllib.request, "urlopen", return_value=Response()) as urlopen:
            hosted.assert_public_repository(
                "https://github.com/example/proofs",
                environ={"GITHUB_TOKEN": token},
            )
        request = urlopen.call_args.args[0]
        self.assertEqual(request.get_header("Authorization"), f"Bearer {token}")
        self.assertEqual(urlopen.call_args.kwargs["timeout"], 30)

        with mock.patch.object(hosted.urllib.request, "urlopen") as unused:
            with self.assertRaisesRegex(hosted.IntakeError, "GITHUB_TOKEN is required") as raised:
                hosted.assert_public_repository(
                    "https://github.com/example/proofs",
                    environ={},
                )
        unused.assert_not_called()
        self.assertNotIn(token, str(raised.exception))

    def test_validate_only_fetches_and_inspects_exact_submission(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = pathlib.Path(tmp)
            make_benchmark(root)
            argv = [
                "--problem-id", "circle",
                "--repository-url", "https://github.com/example/proofs",
                "--commit-sha", "2" * 40,
                "--submission-path", "proof",
                "--model", "human",
                "--benchmark-root", str(root),
                "--validate-only",
            ]
            with mock.patch.object(hosted, "assert_public_repository") as metadata:
                with mock.patch.object(hosted, "validate_exact_submission") as exact:
                    with mock.patch.object(hosted, "prepare_workspace") as prepare:
                        self.assertEqual(hosted.main(argv), 0)
        metadata.assert_called_once_with("https://github.com/example/proofs")
        exact.assert_called_once()
        self.assertEqual(exact.call_args.args[0].commit_sha, "2" * 40)
        self.assertEqual(exact.call_args.args[0].submission_path, "proof")
        prepare.assert_not_called()

    def test_exact_submission_validation_reads_only_proof_allowlist(self) -> None:
        intake = hosted.validate_intake(
            problem_id="circle",
            repository_url="https://github.com/example/proofs",
            commit_sha="2" * 40,
            submission_path="proof",
            model="human",
        )

        def fake_clone(_intake: hosted.Intake, destination: pathlib.Path) -> None:
            proof = destination / "proof"
            (proof / "Submission").mkdir(parents=True)
            (proof / "Submission.lean").write_text("theorem ok : True := trivial\n")
            (proof / "Submission" / "Helper.lean").write_text(
                "theorem helper : True := trivial\n"
            )
            (proof / "lakefile.toml").write_text("malicious = true\n")

        with mock.patch.object(hosted, "clone_exact_commit", side_effect=fake_clone) as clone:
            copied = hosted.validate_exact_submission(intake)
        clone.assert_called_once()
        self.assertEqual(copied, ["Submission.lean", "Submission/Helper.lean"])

    def test_rejects_oversized_public_repository(self) -> None:
        hosted.validate_public_repository_metadata(
            {"private": False, "size": hosted.MAX_REPOSITORY_KIB}
        )
        with self.assertRaisesRegex(hosted.IntakeError, "maximum"):
            hosted.validate_public_repository_metadata(
                {"private": False, "size": hosted.MAX_REPOSITORY_KIB + 1}
            )

    def test_workspace_metadata_is_bound_to_pristine_fingerprint(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = pathlib.Path(tmp)
            fingerprint = make_benchmark(root)
            source = root / "source"
            (source / "Submission").mkdir(parents=True)
            (source / "Submission.lean").write_text("theorem circle : True := trivial\n")
            (source / "Submission" / "Helper.lean").write_text("theorem helper : True := trivial\n")
            intake = hosted.validate_intake(
                problem_id="circle",
                repository_url="https://github.com/example/proofs",
                commit_sha="2" * 40,
                submission_path=".",
                model="human",
            )
            metadata = hosted.prepare_workspace(
                intake=intake,
                benchmark_root=root,
                source_repo=source,
                workspaces_root=root / "workspaces",
            )
            self.assertEqual(metadata["schema_version"], trust.INTAKE_SCHEMA_VERSION)
            self.assertEqual(metadata["problem_fingerprint"], fingerprint)
            self.assertEqual(
                metadata["copied_files"],
                ["Submission.lean", "Submission/Helper.lean"],
            )


class FingerprintTests(unittest.TestCase):
    def test_fingerprint_is_deterministic_ignores_runtime_and_detects_trusted_changes(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = pathlib.Path(tmp)
            initial = make_benchmark(root)
            workspace = root / "generated" / "circle"
            (workspace / "lake-manifest.json").write_text('{"runtime": true}\n')
            (workspace / ".lake" / "build").mkdir(parents=True)
            (workspace / ".lake" / "build" / "cache.olean").write_bytes(b"runtime")
            self.assertEqual(trust.current_problem_fingerprint(root, "circle"), initial)
            (workspace / "Challenge.lean").write_text("theorem circle : False := by sorry\n")
            self.assertNotEqual(trust.current_problem_fingerprint(root, "circle"), initial)

    def test_workflow_context_comes_from_standard_runner_state(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            event = pathlib.Path(tmp) / "event.json"
            event.write_text(json.dumps({"issue": {"number": 19}}), encoding="utf-8")
            context = trust.workflow_context_from_environment(
                {
                    "GITHUB_ACTOR": "alice",
                    "GITHUB_RUN_ATTEMPT": "2",
                    "GITHUB_EVENT_NAME": "issues",
                    "GITHUB_EVENT_PATH": str(event),
                }
            )
            self.assertEqual(context, trust.WorkflowContext("alice", "2", 19, True))
        dispatch = trust.workflow_context_from_environment(
            {
                "GITHUB_ACTOR": "alice",
                "GITHUB_RUN_ATTEMPT": "1",
                "GITHUB_EVENT_NAME": "workflow_dispatch",
            }
        )
        self.assertEqual(dispatch, trust.WorkflowContext("alice", "1", None, False))


class ResultBuilderTests(unittest.TestCase):
    @staticmethod
    def evaluator_payload(*, succeeded: bool, exit_code: int) -> dict[str, object]:
        return {
            "total_problems": 1,
            "attempted_problems": 1,
            "succeeded_problems": int(succeeded),
            "attempted_test_problems": 0,
            "succeeded_test_problems": 0,
            "attempted_main_problems": 1,
            "succeeded_main_problems": int(succeeded),
            "problems": [{
                "id": "circle",
                "title": "Circle",
                "test": False,
                "attempted": True,
                "succeeded": succeeded,
                "exit_code": exit_code,
                "mismatches": ["modified Submission.lean"],
                "workspace_path": "workspaces/circle",
            }],
        }

    def test_evaluator_uses_reserved_rejection_exit_and_fails_closed_otherwise(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            evaluator = pathlib.Path(tmp) / "results.json"
            evaluator.write_text(
                json.dumps(self.evaluator_payload(succeeded=True, exit_code=0)),
                encoding="utf-8",
            )
            self.assertEqual(
                builder.parse_evaluator(evaluator, "circle", process_succeeded=True),
                ("accepted", True),
            )
            self.assertEqual(
                builder.parse_evaluator(evaluator, "circle", process_succeeded=False),
                ("infrastructure_error", False),
            )

            evaluator.write_text(
                json.dumps(self.evaluator_payload(succeeded=False, exit_code=2)),
                encoding="utf-8",
            )
            self.assertEqual(
                builder.parse_evaluator(evaluator, "circle", process_succeeded=True),
                ("rejected", False),
            )

            evaluator.write_text(
                json.dumps(self.evaluator_payload(succeeded=False, exit_code=1)),
                encoding="utf-8",
            )
            self.assertEqual(
                builder.parse_evaluator(evaluator, "circle", process_succeeded=True),
                ("infrastructure_error", False),
            )

    def test_evaluator_requires_complete_consistent_single_problem_summary(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            evaluator = pathlib.Path(tmp) / "results.json"
            malformed: list[object] = [
                [],
                {"problems": []},
                {**self.evaluator_payload(succeeded=True, exit_code=0), "attempted_problems": 0},
                {**self.evaluator_payload(succeeded=True, exit_code=0), "unexpected": True},
            ]
            duplicate = self.evaluator_payload(succeeded=True, exit_code=0)
            duplicate["problems"] = duplicate["problems"] * 2
            malformed.append(duplicate)
            unattempted = self.evaluator_payload(succeeded=False, exit_code=2)
            unattempted["problems"][0]["attempted"] = False
            malformed.append(unattempted)
            for payload in malformed:
                with self.subTest(payload=payload):
                    evaluator.write_text(json.dumps(payload), encoding="utf-8")
                    self.assertEqual(
                        builder.parse_evaluator(
                            evaluator, "circle", process_succeeded=True
                        ),
                        ("infrastructure_error", False),
                    )

            evaluator.write_text("not-json", encoding="utf-8")
            self.assertEqual(
                builder.parse_evaluator(evaluator, "circle", process_succeeded=True),
                ("infrastructure_error", False),
            )

    def test_fingerprint_and_all_comparator_patches_are_in_result(self) -> None:
        fingerprint = "sha256:" + "a" * 64
        result = accepted_result(fingerprint)
        self.assertEqual(result["schema_version"], trust.RESULT_SCHEMA_VERSION)
        self.assertEqual(result["problem_fingerprint"], fingerprint)
        toolchain = result["toolchain"]
        self.assertEqual(
            toolchain["comparator_terminator_patch_sha256"],
            "a421770633877895de509d185a07bf04169a5c9becd73e595315ec95d40f326c",
        )
        self.assertEqual(
            toolchain["comparator_absolute_tools_patch_sha256"],
            "c9796ebf468991d07acc31f2f8e95cef53f61164f03a1ad2302c14f725e2000e",
        )
        self.assertEqual(
            toolchain["comparator_stage_status_patch_sha256"],
            "23a7fa6e34ebc79f2b71576db10f012a32bca85400ca7bf246a7337a3dab9ca2",
        )
        self.assertEqual(
            hashlib.sha256((ROOT / "patches" / "comparator-landrun-terminator.patch").read_bytes()).hexdigest(),
            toolchain["comparator_terminator_patch_sha256"],
        )
        self.assertEqual(
            hashlib.sha256((ROOT / "patches" / "comparator-absolute-tools.patch").read_bytes()).hexdigest(),
            toolchain["comparator_absolute_tools_patch_sha256"],
        )
        self.assertEqual(
            hashlib.sha256((ROOT / "patches" / "comparator-stage-status.patch").read_bytes()).hexdigest(),
            toolchain["comparator_stage_status_patch_sha256"],
        )

    def test_hardened_evaluator_identity_is_in_result(self) -> None:
        toolchain = accepted_result("sha256:" + "a" * 64)["toolchain"]
        self.assertEqual(
            {key: toolchain[key] for key in (
                "runner",
                "lean",
                "lean_archive_sha256",
                "go",
                "go_archive_sha256",
                "mathlib_cache_repo",
                "mathlib_cache_from",
                "runtime_max_sec",
            )},
            {
                "runner": "ubuntu-24.04",
                "lean": "v4.32.2",
                "lean_archive_sha256": (
                    "5f2069e6f5db73780f374ccb49ce8ea649aa20a0cebf0116816744c999ce72aa"
                ),
                "go": "1.25.12",
                "go_archive_sha256": (
                    "234828b7a89e0e303d2556310ee549fbcf253d28de937bac3da13d6294262ac1"
                ),
                "mathlib_cache_repo": "leanprover-community/mathlib4",
                "mathlib_cache_from": "master,legacy",
                "runtime_max_sec": "2700",
            },
        )
        self.assertNotIn("node", toolchain)
        self.assertNotIn("node_archive_sha256", toolchain)

        workflow = (ROOT / ".github" / "workflows" / "submission.yml").read_text(encoding="utf-8")
        lean_installer = (ROOT / "scripts" / "install_pinned_lean.sh").read_text(encoding="utf-8")
        go_installer = (ROOT / "scripts" / "install_pinned_go.sh").read_text(encoding="utf-8")
        self.assertIn(f"runs-on: {toolchain['runner']}", workflow)
        self.assertIn(f"leanprover/lean4:{toolchain['lean']}", lean_installer)
        self.assertIn(toolchain["lean_archive_sha256"], lean_installer)
        self.assertIn(f"GO_VERSION='{toolchain['go']}'", go_installer)
        self.assertIn(toolchain["go_archive_sha256"], go_installer)
        self.assertIn(f"--repo={toolchain['mathlib_cache_repo']}", workflow)
        self.assertIn(f"--cache-from={toolchain['mathlib_cache_from']}", workflow)
        self.assertEqual(workflow.count("lake update"), 1)
        self.assertEqual(
            workflow.count(f"--cache-from={toolchain['mathlib_cache_from']}"), 1
        )
        self.assertIn("scripts/audit_dependency_git.py", workflow)
        self.assertIn(
            'ln -s "$GITHUB_WORKSPACE/.lake/packages" "$workspace/.lake/packages"',
            workflow,
        )
        self.assertNotIn('find -H "$workspace/.lake/packages"', workflow)
        template = (ROOT / "templates" / "WorkspaceTest.lean").read_text(encoding="utf-8")
        runtime_seconds = int(toolchain["runtime_max_sec"])
        self.assertEqual(runtime_seconds % 60, 0)
        self.assertIn(f"RuntimeMaxSec={runtime_seconds // 60}min", template)


class RecordTests(unittest.TestCase):
    def test_append_only_result(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = pathlib.Path(tmp)
            result = accepted_result(make_benchmark(root))
            artifact = root / "result.json"
            raw = (json.dumps(result, sort_keys=True) + "\n").encode()
            artifact.write_bytes(raw)
            digest = root / "result.sha256"
            digest.write_text(hashlib.sha256(raw).hexdigest() + "\n", encoding="utf-8")
            output = root / "results"
            destination = recorder.verify_and_record(
                artifact=artifact,
                digest_file=digest,
                output_dir=output,
                benchmark_root=root,
                expected_run_id="123",
                expected_benchmark_commit="1" * 40,
                workflow_context=trust.WorkflowContext("alice", "1", 7, True),
            )
            self.assertTrue(destination.is_file())
            with self.assertRaises(recorder.ResultError):
                recorder.verify_and_record(
                    artifact=artifact,
                    digest_file=digest,
                    output_dir=output,
                    benchmark_root=root,
                    expected_run_id="123",
                    expected_benchmark_commit="1" * 40,
                    workflow_context=trust.WorkflowContext("alice", "1", 7, True),
                )

    def test_rejects_every_untrusted_binding_field(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = pathlib.Path(tmp)
            result = accepted_result(make_benchmark(root))
            context = trust.WorkflowContext("alice", "1", 7, True)
            cases = {
                "unknown problem": lambda row: row.update(problem_id="other"),
                "stale fingerprint": lambda row: row.update(problem_fingerprint="sha256:" + "0" * 64),
                "wrong toolchain": lambda row: row["toolchain"].update(lean="v0"),
                "wrong actor": lambda row: row.update(actor="mallory"),
                "wrong issue": lambda row: row.update(issue_number=8),
                "ineligible issue": lambda row: row.update(score_eligible=False),
                "wrong attempt": lambda row: row.update(run_attempt="2"),
                "zero attempt": lambda row: row.update(run_attempt="0"),
                "non-proof copied file": lambda row: row.update(copied_files=["Submission.lean", "lakefile.toml"]),
                "duplicate copied file": lambda row: row.update(copied_files=["Submission.lean", "Submission.lean"]),
                "unsorted helpers": lambda row: row.update(copied_files=["Submission.lean", "Submission/Z.lean", "Submission/A.lean"]),
            }
            for label, mutate in cases.items():
                with self.subTest(label=label):
                    candidate = copy.deepcopy(result)
                    mutate(candidate)
                    with self.assertRaises(recorder.ResultError):
                        recorder.validate_result_payload(
                            candidate,
                            benchmark_root=root,
                            expected_run_id="123",
                            expected_benchmark_commit="1" * 40,
                            workflow_context=context,
                        )


class SiteDataTests(unittest.TestCase):
    def test_generates_manifest_titles_and_formalization_inventory(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = pathlib.Path(tmp)
            fingerprint = make_benchmark(root)
            result = accepted_result(fingerprint, run_id="100")
            (root / "results" / "issue-7-run-100-attempt-1.json").write_text(
                json.dumps(result), encoding="utf-8"
            )
            write_formalization_registry(
                root, [{"n": [1, 1], "k": [0, 0]}]
            )

            payloads = site_data.payloads(root)
            leaderboard = payloads[root / "website" / "public" / "data" / "leaderboard.json"]
            self.assertEqual(leaderboard["accepted_problems"][0]["title"], "Circle")
            inventory = leaderboard["formalization_inventory"]
            self.assertEqual(inventory["records"][0]["id"], "test-circle")
            self.assertEqual(inventory["lattice"]["cell_count"], 1)
            self.assertEqual(
                inventory["lattice"]["cells"][0],
                {
                    "n": 1,
                    "k": 0,
                    "record_id": "test-circle",
                    "record_ids": ["test-circle"],
                },
            )

    def test_formalization_ranges_fail_closed(self) -> None:
        cases = {
            "malformed": ([{"n": [1], "k": [0, 0]}], "must be \\[min, max\\]"),
            "out of domain": ([{"n": [0, 1], "k": [0, 0]}], "lies outside"),
            "duplicate": (
                [
                    {"n": [1, 1], "k": [0, 0]},
                    {"n": [1, 1], "k": [0, 0]},
                ],
                "duplicates lattice cell",
            ),
        }
        for label, (ranges, message) in cases.items():
            with self.subTest(label=label), tempfile.TemporaryDirectory() as tmp:
                root = pathlib.Path(tmp)
                make_benchmark(root)
                write_formalization_registry(root, ranges)
                with self.assertRaisesRegex(ValueError, message):
                    site_data.payloads(root)

    def test_only_current_problem_fingerprints_count(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = pathlib.Path(tmp)
            current_fingerprint = make_benchmark(root)
            current = accepted_result(current_fingerprint, run_id="100")
            stale = accepted_result("sha256:" + "0" * 64, run_id="101")
            (root / "results" / "issue-7-run-100-attempt-1.json").write_text(
                json.dumps(current), encoding="utf-8"
            )
            (root / "results" / "issue-7-run-101-attempt-1.json").write_text(
                json.dumps(stale), encoding="utf-8"
            )

            payloads = site_data.payloads(root)
            leaderboard = payloads[root / "website" / "public" / "data" / "leaderboard.json"]
            tracker = payloads[root / "website" / "public" / "data" / "tracker.json"]
            index = payloads[root / "results" / "index.json"]
            self.assertEqual(leaderboard["schema_version"], trust.SITE_SCHEMA_VERSION)
            self.assertEqual(tracker["schema_version"], trust.SITE_SCHEMA_VERSION)
            self.assertEqual(index["schema_version"], trust.SITE_SCHEMA_VERSION)
            self.assertEqual(leaderboard["accepted_eligible_results"], 1)
            self.assertEqual(leaderboard["current_result_count"], 1)
            self.assertEqual(leaderboard["archived_result_count"], 1)
            self.assertEqual(tracker["entries"][0]["formalization_status"], "comparator_verified")
            self.assertEqual(index["result_count"], 1)
            self.assertEqual(index["archived_result_count"], 1)
            self.assertEqual(index["results"][0]["problem_fingerprint"], current_fingerprint)

            (root / "generated" / "circle" / "Challenge.lean").write_text(
                "theorem circle : False := by sorry\n", encoding="utf-8"
            )
            changed = site_data.payloads(root)
            changed_leaderboard = changed[root / "website" / "public" / "data" / "leaderboard.json"]
            changed_tracker = changed[root / "website" / "public" / "data" / "tracker.json"]
            changed_index = changed[root / "results" / "index.json"]
            self.assertEqual(changed_leaderboard["accepted_eligible_results"], 0)
            self.assertEqual(changed_leaderboard["current_result_count"], 0)
            self.assertEqual(changed_leaderboard["archived_result_count"], 2)
            self.assertEqual(changed_tracker["entries"][0]["formalization_status"], "open")
            self.assertEqual(changed_index["result_count"], 0)
            self.assertEqual(changed_index["archived_result_count"], 2)

    def test_incomplete_forged_accepted_result_fails_closed(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = pathlib.Path(tmp)
            fingerprint = make_benchmark(root)
            forged = {
                "schema_version": trust.RESULT_SCHEMA_VERSION,
                "problem_id": "circle",
                "problem_fingerprint": fingerprint,
                "outcome": "accepted",
                "toolchain": dict(trust.EXPECTED_TOOLCHAIN),
            }
            self.assertFalse(
                trust.result_matches_current_benchmark(forged, {"circle": fingerprint})
            )
            (root / "results" / "issue-7-run-999-attempt-1.json").write_text(
                json.dumps(forged), encoding="utf-8"
            )
            with self.assertRaisesRegex(ValueError, "Unexpected stored result fields"):
                site_data.payloads(root)

    def test_stored_result_filename_and_check_bindings_are_strict(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = pathlib.Path(tmp)
            result = accepted_result(make_benchmark(root), run_id="321")
            with self.assertRaisesRegex(trust.TrustError, "filename"):
                trust.validate_stored_result(result, filename="forged.json")
            result["checks"] = {"comparator": True, "lean_kernel": False, "nanoda": True}
            with self.assertRaisesRegex(trust.TrustError, "inconsistent"):
                trust.validate_stored_result(
                    result, filename="issue-7-run-321-attempt-1.json"
                )


if __name__ == "__main__":
    unittest.main()
