from __future__ import annotations

import csv
import hashlib
import json
import pathlib
import subprocess
import sys
import unittest


ROOT = pathlib.Path(__file__).resolve().parents[2]


class ResearchDataTests(unittest.TestCase):
    def test_report_companions_are_reproducible(self) -> None:
        subprocess.run(
            [sys.executable, "scripts/generate_report_companions.py", "--check"],
            cwd=ROOT,
            check=True,
        )

    def test_toda_statement_is_reproducible(self) -> None:
        subprocess.run(
            [sys.executable, "scripts/generate_toda_table.py", "--check"],
            cwd=ROOT,
            check=True,
        )

    def test_lattice_rules_reproduce_committed_counts(self) -> None:
        coverage = json.loads((ROOT / "research/lattice-coverage.json").read_text())
        stems = {
            row["stem"]: row
            for row in json.loads((ROOT / "research/stable-stems.json").read_text())["stems"]
        }
        counts = {
            "exact_integral": 0,
            "published_integral_alternatives": 0,
            "exact_2_primary_only": 0,
            "disputed": 0,
            "not_fully_tabulated": 0,
        }
        for n in range(1, 93):
            for k in range(91):
                if n == 1 or k <= 20:
                    status = "exact_integral"
                elif k <= n - 2:
                    status = (
                        "exact_integral" if stems[k]["is_exact"]
                        else "published_integral_alternatives"
                    )
                elif 21 <= k <= 32 or (
                    k == 33 and (2 <= n <= 9 or 28 <= n <= 34)
                ):
                    status = "exact_2_primary_only"
                elif (n, k) == (27, 33):
                    status = "disputed"
                else:
                    status = "not_fully_tabulated"
                counts[status] += 1
        self.assertEqual(sum(counts.values()), 8372)
        self.assertEqual(counts, coverage["counts"])

    def test_report_and_companion_files_are_present(self) -> None:
        report = ROOT / "website/public/reports/homotopy-groups-of-spheres-literature-review.pdf"
        self.assertEqual(
            hashlib.sha256(report.read_bytes()).hexdigest(),
            "749a0686118c9e4454b6166da0966b8097ba7ebaf2177db198bacd1f7953f9e6",
        )
        with (ROOT / "research/report-data/stable_stems_0_90.csv").open(newline="") as handle:
            stable_rows = list(csv.DictReader(handle))
        with (ROOT / "research/report-data/toda_unstable_stems_0_19.csv").open(newline="") as handle:
            toda_rows = list(csv.DictReader(handle))
        self.assertEqual([int(row["stem"]) for row in stable_rows], list(range(91)))
        self.assertEqual([int(row["stem_k"]) for row in toda_rows], list(range(20)))
        self.assertEqual(toda_rows[0]["n_1"], "infty")
        self.assertEqual(toda_rows[1]["n_1"], "1")
        self.assertEqual(toda_rows[19]["n_20"], "infty+8+2+3+11")
        for name in (
            "stable_stems_0_90.csv",
            "toda_unstable_stems_0_19.csv",
            "homotopy_spheres_bibliography.bib",
        ):
            self.assertEqual(
                (ROOT / "research" / "report-data" / name).read_bytes(),
                (ROOT / "website" / "public" / "reports" / name).read_bytes(),
            )

    def test_formalization_inventory_has_reproducible_provenance(self) -> None:
        inventory = json.loads((ROOT / "research/formalizations.json").read_text())
        entries = inventory["formalizations"]
        self.assertGreaterEqual(len(entries), 5)
        for entry in entries:
            self.assertTrue(entry["source"])
            self.assertTrue(entry["status"])
            self.assertTrue(entry["license"])
        qualified = {entry["id"]: entry["status"] for entry in inventory["qualified_records"]}
        self.assertEqual(
            qualified["lean4-first-stable-wip"], "incomplete_not_a_formalization"
        )


if __name__ == "__main__":
    unittest.main()
