import pathlib
import unittest


ROOT = pathlib.Path(__file__).resolve().parents[2]
PAGES_WORKFLOW = ROOT / ".github" / "workflows" / "pages.yml"


class PagesDeploymentTests(unittest.TestCase):
    def test_successful_submission_workflow_deploys_current_main(self) -> None:
        workflow = PAGES_WORKFLOW.read_text(encoding="utf-8")

        self.assertIn("workflow_run:", workflow)
        self.assertIn("workflows: ['Evaluate submission']", workflow)
        self.assertIn("github.event.workflow_run.conclusion == 'success'", workflow)
        self.assertIn("ref: main", workflow)


if __name__ == "__main__":
    unittest.main()
