from __future__ import annotations

import io
import json
import os
import pathlib
import signal
import sys
import tempfile
import textwrap
import time
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "scripts"))

from security_probes import path_shadow_probe as probe  # noqa: E402


@unittest.skipUnless(os.name == "posix", "process-group probes require POSIX")
class PathShadowProcessTests(unittest.TestCase):
    def assert_process_gone(self, pid: int) -> None:
        deadline = time.monotonic() + 3.0
        while time.monotonic() < deadline:
            try:
                os.kill(pid, 0)
            except ProcessLookupError:
                return
            time.sleep(0.05)
        self.fail(f"process {pid} survived process-group cleanup")

    def test_run_streams_output_and_keeps_only_bounded_diagnostic_tail(self) -> None:
        stream = io.StringIO()
        code = textwrap.dedent(
            """
            import sys
            sys.stdout.write("A" * 4096)
            sys.stdout.flush()
            sys.stderr.write("final diagnostic\\n")
            sys.stderr.flush()
            """
        )
        with tempfile.TemporaryDirectory() as tmp:
            result = probe.run(
                [sys.executable, "-c", code],
                pathlib.Path(tmp),
                timeout=5,
                diagnostic_limit=128,
                output_stream=stream,
            )

        self.assertEqual(result.returncode, 0)
        self.assertEqual(result.stderr, "")
        self.assertEqual(stream.getvalue(), "A" * 4096 + "final diagnostic\n")
        self.assertIn("output truncated to the last 128 characters", result.stdout)
        self.assertIn("final diagnostic", result.stdout)
        self.assertLessEqual(len(result.stdout), 128 + 80)

    def test_timeout_kills_entire_new_process_group_and_preserves_diagnostics(self) -> None:
        stream = io.StringIO()
        with tempfile.TemporaryDirectory() as tmp:
            root = pathlib.Path(tmp)
            state_path = root / "processes.json"
            grandchild_code = textwrap.dedent(
                """
                import os
                import signal
                import time

                signal.signal(signal.SIGTERM, signal.SIG_IGN)
                print("grandchild-ready", flush=True)
                while True:
                    time.sleep(1)
                """
            )
            parent_code = textwrap.dedent(
                f"""
                import json
                import os
                import pathlib
                import signal
                import subprocess
                import sys
                import time

                signal.signal(signal.SIGTERM, signal.SIG_IGN)
                child = subprocess.Popen([sys.executable, "-c", {grandchild_code!r}])
                state = {{
                    "parent_pid": os.getpid(),
                    "parent_session": os.getsid(0),
                    "parent_group": os.getpgrp(),
                    "child_pid": child.pid,
                }}
                pathlib.Path({str(state_path)!r}).write_text(json.dumps(state), encoding="utf-8")
                print("parent-ready", flush=True)
                while True:
                    time.sleep(1)
                """
            )

            state: dict[str, int] = {}
            try:
                with self.assertRaises(probe.ProbeError) as raised:
                    probe.run(
                        [sys.executable, "-c", parent_code],
                        root,
                        timeout=1.0,
                        termination_grace=0.2,
                        output_stream=stream,
                    )
                state = json.loads(state_path.read_text(encoding="utf-8"))

                self.assertEqual(state["parent_pid"], state["parent_session"])
                self.assertEqual(state["parent_pid"], state["parent_group"])
                self.assert_process_gone(state["parent_pid"])
                self.assert_process_gone(state["child_pid"])

                message = str(raised.exception)
                self.assertIn("timed out after 1 seconds", message)
                self.assertIn("SIGTERM then SIGKILL", message)
                self.assertIn("parent-ready", message)
                self.assertIn("grandchild-ready", message)
                self.assertIn("parent-ready", stream.getvalue())
                self.assertIn("grandchild-ready", stream.getvalue())
            finally:
                if state:
                    try:
                        os.killpg(state["parent_group"], signal.SIGKILL)
                    except ProcessLookupError:
                        pass


if __name__ == "__main__":
    unittest.main()
