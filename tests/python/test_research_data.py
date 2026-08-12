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

    def test_comprehensive_frontiers_are_reproducible_and_typed(self) -> None:
        subprocess.run(
            [sys.executable, "scripts/generate_extended_frontiers.py", "--check"],
            cwd=ROOT,
            check=True,
        )
        data = json.loads(
            (ROOT / "website/public/data/extended-frontiers.json").read_text()
        )
        self.assertEqual(data["display"], {"first_stem": 0, "last_stem": 1000})
        self.assertEqual(len(data["integral"]["stems"]), 91)
        self.assertEqual(
            data["integral"]["published_alternative_stems"], [84, 85, 86, 90]
        )

        three = data["three_primary"]
        self.assertEqual([row["stem"] for row in three["stems"]], list(range(109)))
        self.assertEqual(three["stems"][0]["scope"], "3_local_degree_zero")
        self.assertEqual(
            {row["scope"] for row in three["stems"][1:]},
            {"3_primary_torsion_component"},
        )
        self.assertEqual(
            three["coverage"]["positive_stem_primary_components"],
            {"first": 1, "last": 108, "status": "exact"},
        )
        self.assertEqual(three["stems"][91]["group"], "(Z/3)^3")
        self.assertEqual(three["stems"][96]["group"], "0")

        five = data["five_primary_non_j"]
        self.assertEqual(five["entry_count"], 354)
        self.assertEqual(max(row["stem"] for row in five["entries"]), 999)
        self.assertEqual(five["uncertain_stems"], [932, 933, 970, 971])
        self.assertEqual(
            five["quarantined_transcription_stems"],
            [412, 475, 530, 601, 840, 875, 892, 954, 955, 964, 978, 990],
        )
        self.assertIn("does not assert a zero group", five["missing_row_meaning"])
        self.assertTrue(next(row for row in five["entries"] if row["stem"] == 932)["uncertain"])

        image_j = data["image_j_v1"]
        self.assertEqual(image_j["theorem_scope"], "all_stems")
        self.assertEqual(image_j["ledger"], {"first": 0, "last": 1000, "row_count": 1520})
        stem_three = next(row for row in image_j["stems"] if row["stem"] == 3)
        self.assertIn(
            {"prime": "2", "family_type": "2-primary v1-periodic", "group": "Z/8",
             "formula_case": "k=3", "status": "exact"},
            stem_three["entries"],
        )

        height_two = data["height_two_two_primary"]
        self.assertEqual(
            (height_two["grouped_row_count"], height_two["family_count"],
             height_two["residue_count"], height_two["period"]),
            (26, 125, 19, 192),
        )
        filtration_only = [
            row
            for residue in height_two["residues"]
            for row in residue["rows"]
            if "not certified" in row["proof_method"]
        ]
        self.assertEqual(len(filtration_only), 7)
        self.assertEqual(sum(row["family_count"] for row in filtration_only), 19)
        self.assertIn(23, {row["residue"] for row in height_two["residues"]})

        corrections = {row["id"] for row in data["audit_corrections"]}
        self.assertIn("conjecture-ledger-citations-and-ehp-index", corrections)
        ehp = next(
            row for row in data["conjecture_status"]["entries"]
            if row["name"].startswith("Ravenel EHP differential")
        )
        self.assertIn("d_{2^{j-2}}(nu)=eta_j", ehp["statement"])
        conjectures = data["conjecture_status"]["entries"]
        self.assertFalse(
            any(row["source_url"].endswith("/mybooks/ravenel.pdf") for row in conjectures)
        )
        new_doomsday = next(
            row for row in conjectures if row["name"] == "New Doomsday conjecture"
        )
        self.assertEqual(new_doomsday["source_url"], "https://doi.org/10.2307/2374955")
        weak_splitting = next(
            row for row in conjectures
            if row["name"] == "Chromatic splitting conjecture - weak form"
        )
        self.assertEqual(
            weak_splitting["source_url"], "https://doi.org/10.1090/conm/181/02036"
        )

        addenda = json.loads(
            (ROOT / "research/comprehensive-handoff-addenda.json").read_text()
        )
        self.assertEqual(data["research_addenda"], addenda)
        self.assertEqual(addenda["lattice_effect"], "none")
        self.assertEqual(
            (ROOT / "research/comprehensive-handoff-addenda.json").read_bytes(),
            (ROOT / "website/public/reports/comprehensive-2026/addenda.json").read_bytes(),
        )
        expected_addendum_types = {
            "chua-adams-e3-page": "spectral_sequence_computation",
            "carrick-davies-image-j-detection": "stable_detection_theorem",
            "kato-shimomura-local-greek-letters": "chromatic_localization_existence",
            "barratt-priddy-quillen": "foundational_stable_homology_equivalence",
            "bauer-quigley-free-actions": "geometric_existence_family",
            "miyauchi-mukai-toda-relations": (
                "named_toda_bracket_and_composition_relation"
            ),
        }
        addendum_records = {row["id"]: row for row in addenda["records"]}
        self.assertEqual(
            {record_id: row["claim_type"] for record_id, row in addendum_records.items()},
            expected_addendum_types,
        )
        self.assertTrue(
            all(row["lattice_effect"] == "none" for row in addendum_records.values())
        )
        self.assertTrue(
            all(row["primary_url"].startswith("https://") for row in addendum_records.values())
        )
        self.assertTrue(
            all(row["doi"].startswith("10.") for row in addendum_records.values())
        )
        self.assertEqual(
            addendum_records["barratt-priddy-quillen"]["verification_doi"],
            "10.48550/arXiv.2510.13564",
        )

        blocked = json.loads(
            (ROOT / "research/foundation-blocked-results.json").read_text()
        )
        blocked_by_id = {row["id"]: row for row in blocked["targets"]}
        self.assertLessEqual(set(expected_addendum_types), set(blocked_by_id))
        for record_id in expected_addendum_types:
            target = blocked_by_id[record_id]
            self.assertTrue(target["status"].startswith("blocked_on_"))
            self.assertTrue(target["missing"])
            self.assertEqual(target["source_doi"], addendum_records[record_id]["doi"])

    def test_three_primary_statement_is_reproducible(self) -> None:
        subprocess.run(
            [sys.executable, "scripts/generate_three_primary_table.py", "--check"],
            cwd=ROOT,
            check=True,
        )
        manifest = (
            ROOT / "manifests/problems/stable_three_primary_groups_001_108.toml"
        ).read_text()
        self.assertIn("Table A3.2 plus the image-of-J formula", manifest)
        self.assertNotIn("Table A3.4", manifest)

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
        domain = coverage["domain"]
        for n in range(domain["n_min"], domain["n_max"] + 1):
            for k in range(domain["k_min"], domain["k_max"] + 1):
                if n == 1 or k <= 20:
                    status = "exact_integral"
                elif k <= n - 2 and k in stems:
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
        self.assertEqual(sum(counts.values()), domain["cell_count"])
        self.assertEqual(counts, coverage["counts"])
        degree_domain = coverage["degree_domain"]
        self.assertEqual(
            degree_domain["cell_count"],
            (degree_domain["n_max"] - degree_domain["n_min"] + 1)
            * (degree_domain["m_max"] - degree_domain["m_min"] + 1),
        )

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
            self.assertTrue(entry["system"].startswith("Lean 4"))
            self.assertTrue(entry["source"])
            self.assertTrue(entry["status"])
            self.assertTrue(entry["license"])
        qualified = {entry["id"]: entry["status"] for entry in inventory["qualified_records"]}
        self.assertEqual(
            qualified["lean4-first-stable-wip"], "incomplete_not_a_formalization"
        )

        pi2 = next(
            entry for entry in entries
            if entry["id"] == "lean4-benchmark-metric-sphere-pi2"
        )
        self.assertEqual(
            pi2["declarations"],
            ["Submission.pi2_sphere_two_mulEquiv_int"],
        )
        self.assertEqual(
            pi2["lattice_overlay"]["cell_ranges"],
            [{"n": [2, 2], "k": [0, 0]}],
        )

    def test_maintained_set_has_ten_independent_results(self) -> None:
        inventory = json.loads((ROOT / "research/formalizations.json").read_text())
        result_set = inventory["maintained_independent_result_set"]
        results = result_set["results"]
        self.assertEqual(result_set["count"], 10)
        self.assertEqual(len(results), 10)
        self.assertEqual(len({row["id"] for row in results}), 10)
        self.assertEqual(len({row["declaration"] for row in results}), 10)
        self.assertIn("do not count separately", result_set["counting_rule"])
        for result in results:
            source = (ROOT / "research" / result["source"]).resolve()
            self.assertTrue(source.is_file())
            text = source.read_text()
            self.assertNotIn("sorry", text)
            self.assertNotIn("admit", text)
            short_name = result["declaration"].rsplit(".", 1)[-1]
            self.assertIn(f"theorem {short_name}", text)

        circle = next(
            item for item in inventory["formalizations"]
            if item["id"] == "lean4-benchmark-metric-circle-higher"
        )
        self.assertEqual(
            circle["declarations"],
            ["Submission.sphere_one_higher_homotopy_subsingleton"],
        )
        self.assertEqual(len(circle["convenience_corollaries"]), 10)
        suite = next(
            item for item in inventory["formalizations"]
            if item["id"] == "lean4-homotopy-structural-suite"
        )
        self.assertEqual(
            suite["declarations"],
            [row["declaration"] for row in results[1:]],
        )
        self.assertIsNone(suite["lattice_overlay"])

    def test_maintained_twenty_result_set_matches_lean_source(self) -> None:
        inventory = json.loads((ROOT / "research/formalizations.json").read_text())
        result_set = inventory["maintained_lean4_twenty_result_set"]
        results = result_set["results"]
        self.assertEqual(result_set["system"], "Lean 4")
        self.assertEqual(result_set["count"], 20)
        self.assertEqual(len(results), 20)
        self.assertEqual(len({row["id"] for row in results}), 20)
        declarations = [row["declaration"] for row in results]
        self.assertEqual(len(set(declarations)), 20)
        source = (ROOT / "research" / result_set["source"]).resolve()
        self.assertTrue(source.is_file())
        text = source.read_text()
        self.assertNotIn("sorry", text)
        self.assertNotIn("admit", text)
        for declaration in declarations:
            short_name = declaration.rsplit(".", 1)[-1]
            self.assertIn(f"theorem {short_name}", text)

        suite = next(
            item for item in inventory["formalizations"]
            if item["id"] == "lean4-twenty-result-suite"
        )
        self.assertEqual(suite["system"], "Lean 4")
        self.assertEqual(suite["declarations"], declarations)
        self.assertEqual(
            suite["lattice_overlay"]["cell_ranges"],
            [{"n": [1, 1], "k": [0, 90]}],
        )

    def test_higher_sphere_foundation_set_matches_lean_sources(self) -> None:
        inventory = json.loads((ROOT / "research/formalizations.json").read_text())
        result_set = inventory["maintained_higher_sphere_foundation_set"]
        results = result_set["results"]
        self.assertEqual(result_set["system"], "Lean 4")
        self.assertEqual(result_set["count"], 10)
        self.assertEqual(len(results), 10)
        self.assertEqual(len({row["id"] for row in results}), 10)
        self.assertEqual(len({row["declaration"] for row in results}), 10)
        for result in results:
            source = (ROOT / "research" / result["source"]).resolve()
            self.assertTrue(source.is_file())
            text = source.read_text()
            self.assertNotIn("sorry", text)
            self.assertNotIn("admit", text)
            self.assertIn(result["declaration"].rsplit(".", 1)[-1], text)

        suite = next(
            item for item in inventory["formalizations"]
            if item["id"] == "lean4-higher-sphere-foundations"
        )
        self.assertEqual(
            suite["declarations"],
            [row["declaration"] for row in results],
        )
        self.assertIsNone(suite["lattice_overlay"])

    def test_displayed_circle_frontier_is_one_general_lean_result(self) -> None:
        inventory = json.loads((ROOT / "research/formalizations.json").read_text())
        result_set = inventory["maintained_displayed_circle_frontier_set"]
        self.assertEqual(result_set["system"], "Lean 4")
        self.assertEqual(result_set["count"], 1)
        self.assertEqual(len(result_set["results"]), 1)
        source = (ROOT / "research" / result_set["source"]).resolve()
        text = source.read_text()
        self.assertNotIn("sorry", text)
        self.assertNotIn("admit", text)
        declaration = result_set["results"][0]["declaration"].rsplit(".", 1)[-1]
        self.assertIn(f"theorem {declaration}", text)

        frontier = next(
            item for item in inventory["formalizations"]
            if item["id"] == "lean4-displayed-circle-frontier"
        )
        self.assertEqual(
            frontier["lattice_overlay"]["cell_ranges"],
            [{"n": [1, 1], "k": [91, 108]}],
        )
        self.assertEqual(len(frontier["convenience_corollaries"]), 18)

    def test_displayed_lower_connectivity_is_one_general_lean_result(self) -> None:
        inventory = json.loads((ROOT / "research/formalizations.json").read_text())
        result_set = inventory["maintained_displayed_lower_connectivity_set"]
        self.assertEqual(result_set["system"], "Lean 4")
        self.assertEqual(result_set["count"], 1)
        self.assertEqual(len(result_set["results"]), 1)
        source = (ROOT / "research" / result_set["source"]).resolve()
        text = source.read_text()
        self.assertNotIn("sorry", text)
        self.assertNotIn("admit", text)
        declaration = result_set["results"][0]["declaration"].rsplit(".", 1)[-1]
        self.assertIn(f"theorem {declaration}", text)

        record = next(
            item for item in inventory["formalizations"]
            if item["id"] == "lean4-displayed-lower-connectivity"
        )
        self.assertIsNone(record["lattice_overlay"])
        self.assertEqual(
            record["degree_lattice_overlay"]["cell_ranges"],
            [{"n": [2, 92], "m": [1, 91], "where": "m<n"}],
        )

    def test_every_purple_cell_names_and_links_its_exact_lean_witness(self) -> None:
        published = json.loads(
            (ROOT / "website/public/data/leaderboard.json").read_text()
        )["formalization_inventory"]
        for lattice_name in ("lattice", "degree_lattice"):
            cells = published[lattice_name]["cells"]
            self.assertEqual(len(cells), published[lattice_name]["cell_count"])
            for cell in cells:
                self.assertRegex(cell["proof_declaration"], r"^Submission\.[A-Za-z0-9_]+$")
                self.assertRegex(
                    cell["proof_source"],
                    r"^https://github\.com/Vilin97/homotopy-groups-lean/"
                    r"blob/[0-9a-f]{40}/.+\.lean#L[1-9][0-9]*$",
                )

    def test_diagonal_induction_results_match_sorry_free_lean_source(self) -> None:
        inventory = json.loads((ROOT / "research/formalizations.json").read_text())
        result_set = inventory["maintained_diagonal_induction_set"]
        self.assertEqual(result_set["count"], 2)
        self.assertEqual(len(result_set["results"]), 2)
        source = (ROOT / "research" / result_set["source"]).resolve()
        text = source.read_text()
        self.assertNotIn("sorry", text)
        self.assertNotIn("admit", text)
        for result in result_set["results"]:
            declaration = result["declaration"].rsplit(".", 1)[-1]
            self.assertIn(f"theorem {declaration}", text)

        record = next(
            item for item in inventory["formalizations"]
            if item["id"] == "lean4-sphere-diagonal-induction"
        )
        self.assertEqual(
            record["declarations"],
            [result["declaration"] for result in result_set["results"]],
        )
        self.assertIsNone(record["lattice_overlay"])
        self.assertIsNone(record["degree_lattice_overlay"])

    def test_metric_reduced_suspension_bridge_matches_sorry_free_sources(self) -> None:
        inventory = json.loads((ROOT / "research/formalizations.json").read_text())
        result_set = inventory["maintained_metric_reduced_suspension_set"]
        results = result_set["results"]
        self.assertEqual(result_set["system"], "Lean 4")
        self.assertEqual(result_set["count"], 8)
        self.assertEqual(len(results), 8)
        self.assertEqual(len({row["id"] for row in results}), 8)
        self.assertEqual(len({row["declaration"] for row in results}), 8)
        for result in results:
            source = (ROOT / "research" / result["source"]).resolve()
            self.assertTrue(source.is_file())
            text = source.read_text()
            self.assertNotIn("sorry", text)
            self.assertNotIn("admit", text)
            self.assertIn(result["declaration"].rsplit(".", 1)[-1], text)

        record = next(
            item for item in inventory["formalizations"]
            if item["id"] == "lean4-metric-sphere-reduced-suspension"
        )
        self.assertTrue(
            {row["declaration"] for row in results}.issubset(record["declarations"])
        )
        self.assertIsNone(record["lattice_overlay"])
        self.assertIsNone(record["degree_lattice_overlay"])

    def test_sphere_suspension_excision_map_matches_sorry_free_sources(self) -> None:
        inventory = json.loads((ROOT / "research/formalizations.json").read_text())
        result_set = inventory["maintained_sphere_suspension_excision_set"]
        results = result_set["results"]
        self.assertEqual(result_set["system"], "Lean 4")
        self.assertEqual(result_set["count"], 10)
        self.assertEqual(len(results), 10)
        self.assertEqual(len({row["id"] for row in results}), 10)
        self.assertEqual(len({row["declaration"] for row in results}), 10)
        for result in results:
            source = (ROOT / "research" / result["source"]).resolve()
            self.assertTrue(source.is_file())
            text = source.read_text()
            self.assertNotIn("sorry", text)
            self.assertNotIn("admit", text)
            self.assertIn(result["declaration"].rsplit(".", 1)[-1], text)

        record = next(
            item for item in inventory["formalizations"]
            if item["id"] == "lean4-sphere-suspension-excision-map"
        )
        self.assertTrue(
            {row["declaration"] for row in results}.issubset(record["declarations"])
        )
        self.assertEqual(len(record["declarations"]), 22)
        self.assertIsNone(record["lattice_overlay"])
        self.assertIsNone(record["degree_lattice_overlay"])

    def test_sphere_suspension_connectivity_matches_sorry_free_sources(self) -> None:
        inventory = json.loads((ROOT / "research/formalizations.json").read_text())
        result_set = inventory["maintained_sphere_suspension_connectivity_set"]
        results = result_set["results"]
        self.assertEqual(result_set["system"], "Lean 4")
        self.assertEqual(result_set["count"], 7)
        self.assertEqual(len(results), 7)
        self.assertEqual(len({row["id"] for row in results}), 7)
        self.assertEqual(len({row["declaration"] for row in results}), 7)
        for result in results:
            source = (ROOT / "research" / result["source"]).resolve()
            self.assertTrue(source.is_file())
            text = source.read_text()
            self.assertNotIn("sorry", text)
            self.assertNotIn("admit", text)
            self.assertIn(result["declaration"].rsplit(".", 1)[-1], text)

        record = next(
            item for item in inventory["formalizations"]
            if item["id"] == "lean4-sphere-suspension-pair-connectivity"
        )
        self.assertTrue(
            {row["declaration"] for row in results}.issubset(record["declarations"])
        )
        self.assertEqual(len(record["declarations"]), 11)
        self.assertIsNone(record["lattice_overlay"])
        self.assertIsNone(record["degree_lattice_overlay"])

    def test_relative_homology_excision_matches_sorry_free_sources(self) -> None:
        inventory = json.loads((ROOT / "research/formalizations.json").read_text())
        result_set = inventory["maintained_relative_homology_excision_set"]
        results = result_set["results"]
        self.assertEqual(result_set["system"], "Lean 4")
        self.assertEqual(result_set["count"], 13)
        self.assertEqual(len(results), 13)
        self.assertEqual(len({row["id"] for row in results}), 13)
        self.assertEqual(len({row["declaration"] for row in results}), 13)
        for result in results:
            source = (ROOT / "research" / result["source"]).resolve()
            self.assertTrue(source.is_file())
            text = source.read_text()
            self.assertNotIn("sorry", text)
            self.assertNotIn("admit", text)
            self.assertIn(result["declaration"].rsplit(".", 1)[-1], text)

        record = next(
            item for item in inventory["formalizations"]
            if item["id"] == "lean4-relative-homology-excision"
        )
        self.assertTrue(
            {row["declaration"] for row in results}.issubset(record["declarations"])
        )
        self.assertEqual(len(record["declarations"]), 49)
        self.assertEqual(record["commit"], "83ca026b579a3331bcc990d9fb3058c7711c69b8")
        self.assertIsNone(record["lattice_overlay"])
        self.assertIsNone(record["degree_lattice_overlay"])

    def test_connected_pair_homology_vanishing_matches_sorry_free_sources(self) -> None:
        inventory = json.loads((ROOT / "research/formalizations.json").read_text())
        result_set = inventory["maintained_connected_pair_homology_set"]
        results = result_set["results"]
        self.assertEqual(result_set["system"], "Lean 4")
        self.assertEqual(result_set["count"], 6)
        self.assertEqual(len(results), 6)
        self.assertEqual(len({row["id"] for row in results}), 6)
        self.assertEqual(len({row["declaration"] for row in results}), 6)
        for result in results:
            source = (ROOT / "research" / result["source"]).resolve()
            self.assertTrue(source.is_file())
            text = source.read_text()
            self.assertNotIn("sorry", text)
            self.assertNotIn("admit", text)
            self.assertIn(result["declaration"].rsplit(".", 1)[-1], text)

        record = next(
            item for item in inventory["formalizations"]
            if item["id"] == "lean4-connected-pair-homology-vanishing"
        )
        self.assertTrue(
            {row["declaration"] for row in results}.issubset(record["declarations"])
        )
        self.assertEqual(len(record["declarations"]), 7)
        self.assertEqual(record["commit"], "846469caceea83cc00a2a4e41a64ae79dc0b7925")
        self.assertIsNone(record["lattice_overlay"])
        self.assertIsNone(record["degree_lattice_overlay"])

    def test_relative_hurewicz_comparison_matches_sorry_free_sources(self) -> None:
        inventory = json.loads((ROOT / "research/formalizations.json").read_text())
        result_set = inventory["maintained_relative_hurewicz_comparison_set"]
        results = result_set["results"]
        self.assertEqual(result_set["system"], "Lean 4")
        self.assertEqual(result_set["count"], 8)
        self.assertEqual(len(results), 8)
        self.assertEqual(len({row["id"] for row in results}), 8)
        self.assertEqual(len({row["declaration"] for row in results}), 8)
        for result in results:
            source = (ROOT / "research" / result["source"]).resolve()
            self.assertTrue(source.is_file())
            text = source.read_text()
            self.assertNotIn("sorry", text)
            self.assertNotIn("admit", text)
            self.assertIn(result["declaration"].rsplit(".", 1)[-1], text)

        record = next(
            item for item in inventory["formalizations"]
            if item["id"] == "lean4-relative-hurewicz-comparison"
        )
        self.assertTrue(
            {row["declaration"] for row in results}.issubset(record["declarations"])
        )
        self.assertEqual(len(record["declarations"]), 20)
        self.assertEqual(record["commit"], "09443093f6a6c3d21a20ea4d7e7fe7c69bafa2b6")
        self.assertIsNone(record["lattice_overlay"])
        self.assertIsNone(record["degree_lattice_overlay"])

    def test_first_hurewicz_normalization_matches_sorry_free_sources(self) -> None:
        inventory = json.loads((ROOT / "research/formalizations.json").read_text())
        result_set = inventory["maintained_first_hurewicz_normalization_set"]
        results = result_set["results"]
        self.assertEqual(result_set["system"], "Lean 4")
        self.assertEqual(result_set["count"], 8)
        self.assertEqual(len(results), 8)
        self.assertEqual(len({row["id"] for row in results}), 8)
        self.assertEqual(len({row["declaration"] for row in results}), 8)
        for result in results:
            source = (ROOT / "research" / result["source"]).resolve()
            self.assertTrue(source.is_file())
            text = source.read_text()
            self.assertNotIn("sorry", text)
            self.assertNotIn("admit", text)
            self.assertIn(result["declaration"].rsplit(".", 1)[-1], text)

        record = next(
            item for item in inventory["formalizations"]
            if item["id"] == "lean4-first-hurewicz-normalization"
        )
        self.assertTrue(
            {row["declaration"] for row in results}.issubset(record["declarations"])
        )
        self.assertEqual(len(record["declarations"]), 19)
        self.assertEqual(record["commit"], "18b2027164dd7b82588fbc008656dd65130bff7f")
        self.assertIsNone(record["lattice_overlay"])
        self.assertIsNone(record["degree_lattice_overlay"])

    def test_first_hurewicz_simplex_class_matches_sorry_free_sources(self) -> None:
        inventory = json.loads((ROOT / "research/formalizations.json").read_text())
        result_set = inventory["maintained_first_hurewicz_simplex_class_set"]
        results = result_set["results"]
        self.assertEqual(result_set["system"], "Lean 4")
        self.assertEqual(result_set["count"], 10)
        self.assertEqual(len(results), 10)
        self.assertEqual(len({row["id"] for row in results}), 10)
        self.assertEqual(len({row["declaration"] for row in results}), 10)
        for result in results:
            source = (ROOT / "research" / result["source"]).resolve()
            self.assertTrue(source.is_file())
            text = source.read_text()
            self.assertNotIn("sorry", text)
            self.assertNotIn("admit", text)
            self.assertIn(result["declaration"].rsplit(".", 1)[-1], text)

        record = next(
            item for item in inventory["formalizations"]
            if item["id"] == "lean4-first-hurewicz-simplex-class"
        )
        self.assertTrue(
            {row["declaration"] for row in results}.issubset(record["declarations"])
        )
        self.assertEqual(len(record["declarations"]), 33)
        self.assertEqual(record["commit"], "976fe9ba5e9e224044fe43b2bac4ea4b1d3d9817")
        self.assertIsNone(record["lattice_overlay"])
        self.assertIsNone(record["degree_lattice_overlay"])

    def test_first_hurewicz_orientation_matches_sorry_free_sources(self) -> None:
        inventory = json.loads((ROOT / "research/formalizations.json").read_text())
        result_set = inventory["maintained_first_hurewicz_orientation_set"]
        results = result_set["results"]
        self.assertEqual(result_set["system"], "Lean 4")
        self.assertEqual(result_set["count"], 10)
        self.assertEqual(len(results), 10)
        self.assertEqual(len({row["id"] for row in results}), 10)
        self.assertEqual(len({row["declaration"] for row in results}), 10)
        for result in results:
            source = (ROOT / "research" / result["source"]).resolve()
            self.assertTrue(source.is_file())
            text = source.read_text()
            self.assertNotIn("sorry", text)
            self.assertNotIn("admit", text)
            self.assertIn(result["declaration"].rsplit(".", 1)[-1], text)

        record = next(
            item for item in inventory["formalizations"]
            if item["id"] == "lean4-first-hurewicz-orientation"
        )
        self.assertTrue(
            {row["declaration"] for row in results}.issubset(record["declarations"])
        )
        self.assertEqual(len(record["declarations"]), 25)
        self.assertEqual(record["commit"], "88f30fcda997350106a5dcb698f86b1db76f2ebf")
        self.assertIsNone(record["lattice_overlay"])
        self.assertIsNone(record["degree_lattice_overlay"])


if __name__ == "__main__":
    unittest.main()
