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
        lean_text = (ROOT / "HomotopyGroups/TodaVerified.lean").read_text()
        for theorem_name in (
            "toda_unstable_integral_diagonal",
            "toda_unstable_integral_circle_positive",
        ):
            start = lean_text.index(f"theorem {theorem_name}")
            end = lean_text.find("\n/--", start)
            if end == -1:
                end = len(lean_text)
            theorem_text = lean_text[start:end]
            self.assertNotIn("sorry", theorem_text)
            self.assertNotIn("admit", theorem_text)
        generated_text = (ROOT / "HomotopyGroups/TodaTable.lean").read_text()
        full_start = generated_text.index("theorem toda_unstable_integral_table")
        self.assertIn("sorry", generated_text[full_start:])
        inventory = json.loads((ROOT / "research/formalizations.json").read_text())
        record = next(
            item for item in inventory["formalizations"]
            if item["id"] == "lean4-toda-verified-diagonal-and-circle"
        )
        self.assertEqual(
            record["declarations"],
            [
                "HomotopyGroups.toda_unstable_integral_diagonal",
                "HomotopyGroups.toda_unstable_integral_circle_positive",
            ],
        )
        self.assertEqual(
            record["commit"],
            "6e1b90e9c061eab71bd6ec933c217f301b81395e",
        )
        self.assertIsNone(record["lattice_overlay"])
        self.assertIsNone(record["degree_lattice_overlay"])

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
            [
                "Submission.pi2_sphere_two_mulEquiv_int",
                "HomotopyGroups.StableStems.stable_stem_000",
            ],
        )
        self.assertEqual(
            pi2["commit"],
            "cf6935bdaa668ad24e2a74f26540236f098dc670",
        )
        self.assertEqual(
            pi2["lattice_overlay"]["cell_ranges"],
            [{"n": [2, 2], "k": [0, 0]}],
        )
        self.assertEqual(pi2["lattice_overlay"]["proof"]["line"], 24)
        wrapper = (
            ROOT
            / "examples/submissions/sphere_lower_homotopy_subsingleton/Submission"
            / "Pi2SphereTwo.lean"
        )
        generic = wrapper.with_name("Pi2SphereTwoGeneric.lean")
        for source in (wrapper, generic):
            text = source.read_text()
            self.assertNotIn("sorry", text)
            self.assertNotIn("admit", text)
        stable_text = (ROOT / "HomotopyGroups/StableStems.lean").read_text()
        start = stable_text.index("theorem stable_stem_000")
        end = stable_text.index("\n/--", start)
        self.assertNotIn("sorry", stable_text[start:end])
        self.assertIn(
            "knowledge_status=formalized_local",
            (ROOT / "manifests/problems/stable_stem_000.toml").read_text(),
        )

        circle = next(
            entry for entry in entries
            if entry["id"] == "lean4-benchmark-metric-circle-pi1"
        )
        self.assertEqual(
            circle["declarations"],
            [
                "Submission.pi1_circle_mulEquiv_int",
                "Submission.pi1_sph_one_at_mulEquiv_int",
                "Submission.pi1_sphere_one_mulEquiv_int",
                "HomotopyGroups.pi1_circle_mulEquiv_int",
            ],
        )
        self.assertEqual(
            circle["commit"],
            "a2578f3038f418a99d89b87691f2abdd60e7c2f2",
        )
        self.assertEqual(circle["lattice_overlay"]["proof"]["line"], 37)
        circle_wrapper = (
            ROOT
            / "examples/submissions/sphere_lower_homotopy_subsingleton/Submission"
            / "MetricSpherePiOne.lean"
        )
        for source in (circle_wrapper, circle_wrapper.with_name("MetricSpherePiOneGeneric.lean")):
            text = source.read_text()
            self.assertNotIn("sorry", text)
            self.assertNotIn("admit", text)
        spaces_text = (ROOT / "HomotopyGroups/Spaces.lean").read_text()
        start = spaces_text.index("theorem pi1_circle_mulEquiv_int")
        end = spaces_text.index("\n@[eval_problem]", start)
        self.assertNotIn("sorry", spaces_text[start:end])

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
            [
                "Submission.sphere_one_higher_homotopy_subsingleton",
                "Submission.sph_one_higher_homotopy_subsingleton_at",
                "Submission.sphere_one_higher_homotopy_subsingleton_at",
                "HomotopyGroups.sphere_one_higher_homotopy_subsingleton",
            ],
        )
        self.assertEqual(
            circle["commit"],
            "bb372606cd4a1670a66b4fd7609a7eee6a3a6b4f",
        )
        self.assertEqual(len(circle["convenience_corollaries"]), 10)
        generic = (
            ROOT
            / "examples/submissions/sphere_lower_homotopy_subsingleton/Submission"
            / "MetricSpherePiOneGeneric.lean"
        )
        generic_text = generic.read_text()
        self.assertNotIn("sorry", generic_text)
        self.assertNotIn("admit", generic_text)
        canonical_text = (ROOT / "HomotopyGroups/LiteratureReview.lean").read_text()
        start = canonical_text.index("theorem sphere_one_higher_homotopy_subsingleton")
        end = canonical_text.index("\n/--", start)
        self.assertNotIn("sorry", canonical_text[start:end])
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

        canonical = next(
            item for item in inventory["formalizations"]
            if item["id"] == "lean4-metric-sphere-connectivity"
        )
        self.assertEqual(
            canonical["declarations"],
            [
                "Submission.subsingleton_homotopyGroup_sphere_of_lt",
                "HomotopyGroups.sphere_lower_homotopy_subsingleton",
            ],
        )
        self.assertEqual(
            canonical["commit"],
            "82a6ce0f1491a67af6336f0145f0a1178dadac0c",
        )
        spaces_text = (ROOT / "HomotopyGroups/Spaces.lean").read_text()
        start = spaces_text.index("theorem sphere_lower_homotopy_subsingleton")
        end = spaces_text.index("\n@[eval_problem]", start)
        self.assertNotIn("sorry", spaces_text[start:end])
        self.assertIn(
            "knowledge_status=formalized_local",
            (ROOT / "manifests/problems/sphere_lower_homotopy_subsingleton.toml").read_text(),
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

    def test_hurewicz_naturality_cap_reduction_matches_sources(self) -> None:
        inventory = json.loads((ROOT / "research/formalizations.json").read_text())
        result_set = inventory["maintained_hurewicz_naturality_cap_set"]
        results = result_set["results"]
        self.assertEqual(result_set["system"], "Lean 4")
        self.assertEqual(result_set["count"], 4)
        self.assertEqual(len(results), 4)
        self.assertEqual(len({row["id"] for row in results}), 4)
        self.assertEqual(len({row["declaration"] for row in results}), 4)
        for result in results:
            source = (ROOT / "research" / result["source"]).resolve()
            self.assertTrue(source.is_file())
            text = source.read_text()
            self.assertNotIn("sorry", text)
            self.assertNotIn("admit", text)
            self.assertIn(result["declaration"].rsplit(".", 1)[-1], text)

        record = next(
            item for item in inventory["formalizations"]
            if item["id"] == "lean4-hurewicz-naturality-cap-reduction"
        )
        self.assertEqual(
            record["declarations"],
            [
                "Submission.singletonBasedPairMap",
                "Submission.singletonToBasedPair",
                "Submission.relativeHurewicz_jStar",
                "Submission.absoluteHurewiczAdd_naturality",
                "Submission.IsNConnected.relativeHurewiczAdd_bijective_of_contractibleSubspace",
                "Submission.sphereSuspensionTargetRelativeHurewiczAdd_bijective",
                "Submission.sphereSuspensionTargetRelativeHurewiczAddEquiv",
                "Submission.sphereSuspensionExcision_relativeHurewicz_naturality",
                "Submission.sphereSuspensionExcisionHom_bijective_iff_sourceRelativeHurewiczAdd",
            ],
        )
        self.assertEqual(
            record["commit"],
            "158af4d670c9f9a1200d3e45ded978cc15d1949e",
        )
        self.assertIsNone(record["lattice_overlay"])
        self.assertIsNone(record["degree_lattice_overlay"])

    def test_cubical_hurewicz_cap_excision_matches_sources(self) -> None:
        inventory = json.loads((ROOT / "research/formalizations.json").read_text())
        result_set = inventory["maintained_cubical_hurewicz_cap_excision_set"]
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
            if item["id"] == "lean4-cubical-hurewicz-cap-excision"
        )
        self.assertEqual(
            record["declarations"],
            [
                "Submission.GenLoop.cubicalBoundaryExtension_map",
                "Submission.GenLoop.cubicalBoundaryHurewicz_map",
                "Submission.relativeHurewicz_mk_boundary_cubical",
                "Submission.cubeBoundaryJarCollapse_eq_iff",
                "Submission.cubeBoundaryJarCollapseHomotopyEquiv",
                "Submission.cubicalBoundarySphereGeneratorCoordinate_eq_one_or_neg_one",
                "Submission.absoluteHurewiczSphereGeneratorCoordinate_eq_one_or_neg_one",
                "Submission.cubicalBoundaryAbsoluteSign_eq_one_or_neg_one",
                "Submission.cubicalBoundaryHurewicz_sphereGenerator",
                "Submission.genLoop_map_sphereGenerator_targetGenLoopSphereMap",
                "Submission.cubicalBoundaryHurewicz_eq_sign_smul_absolute",
                "Submission.IsNConnected.relativeHurewiczAdd_bijective_of_contractibleAmbient",
                "Submission.sphereSuspensionSourceRelativeHurewiczAdd_bijective_succ",
                "Submission.sphereSuspensionExcisionHom_bijective_succ",
                "Submission.sphere_diagonal_mulEquiv_int_via_capExcision",
            ],
        )
        self.assertEqual(
            record["commit"],
            "041d2ac4d1beaf3d78777c1885f3522b0bb4a3a8",
        )
        self.assertIsNone(record["lattice_overlay"])
        self.assertIsNone(record["degree_lattice_overlay"])

    def test_cubical_hurewicz_degree_one_matches_sources(self) -> None:
        inventory = json.loads((ROOT / "research/formalizations.json").read_text())
        result_set = inventory["maintained_cubical_hurewicz_degree_one_set"]
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
            if item["id"] == "lean4-cubical-hurewicz-degree-one"
        )
        self.assertEqual(
            record["declarations"],
            [
                "Submission.pathSimplex_map",
                "Submission.CsingMap_edge",
                "Submission.HgrpMap_loopH",
                "Submission.hurewiczOnePi_of_genLoop",
                "Submission.genLoopEquivOfUnique_map",
                "Submission.hurewiczOnePi_of_genLoop_naturality",
                "Submission.cubicalBoundarySphereGeneratorOneCoordinate_eq_one_or_neg_one",
                "Submission.hurewiczOneSphereGeneratorCoordinate_eq_one_or_neg_one",
                "Submission.cubicalBoundaryHurewiczOneSign_eq_one_or_neg_one",
                "Submission.cubicalBoundaryHurewicz_sphereGenerator_one",
                "Submission.cubicalBoundaryHurewicz_eq_sign_smul_hurewiczOne",
                "Submission.IsNConnected.relativeHurewiczAdd_bijective_of_contractibleAmbient_one",
                "Submission.sphereSuspensionExcisionHom_bijective_zero",
                "Submission.sphereSuspensionExcisionHom_bijective",
                "Submission.sphere_diagonal_mulEquiv_int_via_all_capExcision",
            ],
        )
        self.assertEqual(
            record["commit"],
            "bdaa64166f3ce457864662198e83376760b37103",
        )
        self.assertIsNone(record["lattice_overlay"])
        self.assertIsNone(record["degree_lattice_overlay"])

    def test_diagonal_reduced_suspension_bijectivity_matches_sources(self) -> None:
        inventory = json.loads((ROOT / "research/formalizations.json").read_text())
        result_set = inventory[
            "maintained_diagonal_reduced_suspension_bijectivity_set"
        ]
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
            if item["id"] == "lean4-diagonal-reduced-suspension-bijective"
        )
        self.assertEqual(
            record["declarations"],
            [
                "Submission.cubeToSphere_eq_sphereBasepoint_iff",
                "Submission.reducedSuspensionSphereGenerator_collapsed_iff",
                "Submission.reducedSuspensionSphereGeneratorLoop_eq_iff",
                "Submission.reducedSuspensionSphereGeneratorLoop_surjective",
                "Submission.sphereDiagonalReducedSuspensionGeneratorLoop_eq_iff",
                "Submission.sphereDiagonalReducedSuspensionGeneratorLoop_surjective",
                "Submission.sphereDiagonalReducedSuspensionGeneratorMap_basepoint",
                "Submission.sphereDiagonalReducedSuspensionGeneratorMap_bijective",
                "Submission.sphereDiagonalReducedSuspensionGeneratorHomeomorph",
                "Submission.forall_mem_zpowers_map_mulEquiv",
                "Submission.forall_mem_zpowers_of_mulEquiv_int_unit",
                "Submission.MonoidHom.bijective_of_maps_infinite_cyclic_generators",
                "Submission.sphereDiagonalHurewiczMulEquiv_generator",
                "Submission.sphereGeneratorClass_generates_succ",
                "Submission.sphereOneHurewiczMulEquiv_generator",
                "Submission.sphereGeneratorClass_generates_one",
                "Submission.sphereGeneratorClass_generates",
                "Submission.sphereDiagonalReducedSuspensionHom_generator",
                "Submission.sphereDiagonalReducedSuspensionHom_generator_generates",
                "Submission.sphereDiagonalReducedSuspensionHom_bijective",
                "Submission.sphereDiagonalReducedSuspensionEquiv",
                "Submission.sphere_diagonal_mulEquiv_int_via_reducedSuspension",
            ],
        )
        self.assertEqual(
            record["commit"],
            "68692f8c97791a22da29492ba343304f0358249f",
        )
        self.assertIsNone(record["lattice_overlay"])
        self.assertIsNone(record["degree_lattice_overlay"])

    def test_reduced_suspension_stable_transport_matches_source(self) -> None:
        inventory = json.loads((ROOT / "research/formalizations.json").read_text())
        result_set = inventory[
            "maintained_reduced_suspension_stable_transport_set"
        ]
        results = result_set["results"]
        self.assertEqual(result_set["system"], "Lean 4")
        self.assertEqual(result_set["count"], 3)
        self.assertEqual(len(results), 3)
        self.assertEqual(len({row["id"] for row in results}), 3)
        self.assertEqual(len({row["declaration"] for row in results}), 3)
        for result in results:
            source = (ROOT / "research" / result["source"]).resolve()
            self.assertTrue(source.is_file())
            text = source.read_text()
            self.assertNotIn("sorry", text)
            self.assertNotIn("admit", text)
            self.assertIn(result["declaration"].rsplit(".", 1)[-1], text)

        record = next(
            item for item in inventory["formalizations"]
            if item["id"] == "lean4-reduced-suspension-stable-transport"
        )
        self.assertEqual(
            record["declarations"],
            [
                "Submission.sphereReducedSuspensionPiHom",
                "Submission.sphereReducedSuspensionPiEquiv",
                "Submission.sphereReducedSuspensionPiHom_diagonal",
                "Submission.sphereReducedSuspensionPiHom_bijective_diagonal",
                "Submission.sphereStemReducedSuspensionHom",
                "Submission.sphereStemReducedSuspensionEquiv",
                "Submission.sphereStemReducedSuspensionHom_zero",
                "Submission.sphereStemReducedSuspensionHom_bijective_zero",
                "Submission.nonempty_sphereReducedSuspensionPiIterEquiv",
                "Submission.nonempty_sphereStemReducedSuspensionIterEquiv",
                "Submission.sphere_stem_mulEquiv_of_reduced_suspension",
                "Submission.sphere_stable_stem_mulEquiv_of_reduced_suspension",
                "Submission.nonempty_sphereStemReducedSuspensionIterEquiv_zero",
            ],
        )
        self.assertEqual(
            record["commit"],
            "66d9730987fb4b1d1a8fd25737e3922eee479164",
        )
        self.assertIsNone(record["lattice_overlay"])
        self.assertIsNone(record["degree_lattice_overlay"])

    def test_exact_hopf_map_foundation_matches_source(self) -> None:
        inventory = json.loads((ROOT / "research/formalizations.json").read_text())
        result_set = inventory["maintained_hopf_map_foundation_set"]
        results = result_set["results"]
        self.assertEqual(result_set["system"], "Lean 4")
        self.assertEqual(result_set["count"], 5)
        self.assertEqual(len(results), 5)
        self.assertEqual(len({row["id"] for row in results}), 5)
        self.assertEqual(len({row["declaration"] for row in results}), 5)
        for result in results:
            source = (ROOT / "research" / result["source"]).resolve()
            self.assertTrue(source.is_file())
            text = source.read_text()
            self.assertNotIn("sorry", text)
            self.assertNotIn("admit", text)
            self.assertIn(result["declaration"].rsplit(".", 1)[-1], text)

        record = next(
            item for item in inventory["formalizations"]
            if item["id"] == "lean4-exact-hopf-map-foundation"
        )
        self.assertEqual(
            record["declarations"],
            [
                "Submission.hopfVec",
                "Submission.norm_hopfVec_sq",
                "Submission.continuous_hopfVec",
                "Submission.hopfMap",
                "Submission.hopfMap_basepoint",
                "Submission.hopfCircleIncl",
                "Submission.hopfMap_hopfCircleIncl",
                "Submission.hopfFiberBasepoint",
                "Submission.hopfFiber_last_coords",
                "Submission.hopfMap_eq_basepoint_iff",
                "Submission.circleToHopfFiber",
                "Submission.hopfFiberToCircle",
                "Submission.circleHomeomorphHopfFiber",
                "Submission.circleHomeomorphHopfFiber_basepoint",
                "Submission.hopfFiber_higher_homotopy_subsingleton",
                "Submission.hopfPiThreeHom",
                "Submission.hopfPiThreeHom_bijective",
                "Submission.hopfPiThreeEquiv",
                "Submission.pi3_sphere_two_mulEquiv_int_of_hopf_isSerreFibration",
            ],
        )
        self.assertEqual(
            record["commit"],
            "5b98ed5aecbe77d95eb754b132c314425a60f473",
        )
        self.assertIsNone(record["lattice_overlay"])
        self.assertIsNone(record["degree_lattice_overlay"])

    def test_exact_hopf_local_trivializations_match_source(self) -> None:
        inventory = json.loads((ROOT / "research/formalizations.json").read_text())
        result_set = inventory["maintained_hopf_local_trivialization_set"]
        results = result_set["results"]
        self.assertEqual(result_set["system"], "Lean 4")
        self.assertEqual(result_set["count"], 4)
        self.assertEqual(len(results), 4)
        self.assertEqual(len({row["id"] for row in results}), 4)
        self.assertEqual(len({row["declaration"] for row in results}), 4)
        for result in results:
            source = (ROOT / "research" / result["source"]).resolve()
            self.assertTrue(source.is_file())
            text = source.read_text()
            self.assertNotIn("sorry", text)
            self.assertNotIn("admit", text)
            self.assertIn(result["declaration"].rsplit(".", 1)[-1], text)

        record = next(
            item for item in inventory["formalizations"]
            if item["id"] == "lean4-exact-hopf-local-trivializations"
        )
        self.assertEqual(len(record["declarations"]), 23)
        self.assertEqual(
            record["commit"],
            "1e052eb5195ea62bbb848cfb8484132e204c58e1",
        )
        source = (ROOT / "research" / record["source"]).resolve()
        text = source.read_text()
        self.assertNotIn("sorry", text)
        self.assertNotIn("admit", text)
        for declaration in record["declarations"]:
            self.assertIn(declaration.rsplit(".", 1)[-1], text)
        self.assertIsNone(record["lattice_overlay"])
        self.assertIsNone(record["degree_lattice_overlay"])

    def test_exact_hopf_fibration_and_transport_match_sources(self) -> None:
        inventory = json.loads((ROOT / "research/formalizations.json").read_text())
        result_set = inventory["maintained_hopf_fibration_set"]
        results = result_set["results"]
        self.assertEqual(result_set["system"], "Lean 4")
        self.assertEqual(result_set["count"], 5)
        self.assertEqual(len(results), 5)
        self.assertEqual(len({row["id"] for row in results}), 5)
        self.assertEqual(len({row["declaration"] for row in results}), 5)
        for result in results:
            source = (ROOT / "research" / result["source"]).resolve()
            self.assertTrue(source.is_file())
            text = source.read_text()
            self.assertIn(result["declaration"].rsplit(".", 1)[-1], text)
            if source.name != "Spaces.lean":
                self.assertNotIn("sorry", text)
                self.assertNotIn("admit", text)

        transport_record = next(
            item for item in inventory["formalizations"]
            if item["id"] == "lean4-exact-hopf-short-transport"
        )
        self.assertEqual(len(transport_record["declarations"]), 23)
        self.assertEqual(
            transport_record["commit"],
            "b10572391470375d6140e5cc64f2fe3baf8e6603",
        )
        transport_source = (ROOT / "research" / transport_record["source"]).resolve()
        transport_text = transport_source.read_text()
        self.assertNotIn("sorry", transport_text)
        self.assertNotIn("admit", transport_text)
        for declaration in transport_record["declarations"]:
            self.assertIn(declaration.rsplit(".", 1)[-1], transport_text)
        self.assertIsNone(transport_record["lattice_overlay"])
        self.assertIsNone(transport_record["degree_lattice_overlay"])

        fibration_record = next(
            item for item in inventory["formalizations"]
            if item["id"] == "lean4-exact-hopf-serre-fibration"
        )
        self.assertEqual(len(fibration_record["declarations"]), 21)
        self.assertEqual(
            fibration_record["commit"],
            "b10572391470375d6140e5cc64f2fe3baf8e6603",
        )
        fibration_source = (ROOT / "research" / fibration_record["source"]).resolve()
        fibration_text = fibration_source.read_text()
        self.assertNotIn("sorry", fibration_text)
        self.assertNotIn("admit", fibration_text)
        for declaration in fibration_record["declarations"]:
            self.assertIn(declaration.rsplit(".", 1)[-1], fibration_text)
        self.assertEqual(
            fibration_record["lattice_overlay"]["cell_ranges"],
            [{"n": [2, 2], "k": [1, 1]}],
        )
        self.assertIsNone(fibration_record["degree_lattice_overlay"])

        higher_set = inventory["maintained_hopf_higher_equivalence_set"]
        self.assertEqual(higher_set["system"], "Lean 4")
        self.assertEqual(higher_set["count"], 2)
        self.assertEqual(len(higher_set["results"]), 2)
        higher_record = next(
            item for item in inventory["formalizations"]
            if item["id"] == "lean4-hopf-higher-homotopy-equivalences"
        )
        self.assertEqual(len(higher_record["declarations"]), 6)
        self.assertEqual(
            higher_record["commit"],
            "e639844e7c171da9d5a1cda9f77d11177b95e91c",
        )
        higher_source = (ROOT / "research" / higher_record["source"]).resolve()
        higher_text = higher_source.read_text()
        self.assertNotIn("sorry", higher_text)
        self.assertNotIn("admit", higher_text)
        for declaration in higher_record["declarations"]:
            self.assertIn(declaration.rsplit(".", 1)[-1], higher_text)
        self.assertIsNone(higher_record["lattice_overlay"])
        self.assertIsNone(higher_record["degree_lattice_overlay"])

        spaces = (ROOT / "HomotopyGroups/Spaces.lean").read_text()
        self.assertIn("Submission.pi3_sphere_two_mulEquiv_int", spaces)

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

    def test_first_hurewicz_surjectivity_matches_sorry_free_sources(self) -> None:
        inventory = json.loads((ROOT / "research/formalizations.json").read_text())
        result_set = inventory["maintained_first_hurewicz_surjectivity_set"]
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
            if item["id"] == "lean4-first-relative-hurewicz-surjectivity"
        )
        self.assertTrue(
            {row["declaration"] for row in results}.issubset(record["declarations"])
        )
        self.assertEqual(len(record["declarations"]), 54)
        self.assertEqual(record["commit"], "10c2bcd54cd3b59785fb45b324b8526641ded2d7")
        self.assertIsNone(record["lattice_overlay"])
        self.assertIsNone(record["degree_lattice_overlay"])

    def test_normalized_simplex_boundary_matches_sorry_free_sources(self) -> None:
        inventory = json.loads((ROOT / "research/formalizations.json").read_text())
        result_set = inventory["maintained_normalized_simplex_boundary_set"]
        results = result_set["results"]
        self.assertEqual(result_set["system"], "Lean 4")
        self.assertEqual(result_set["count"], 9)
        self.assertEqual(len(results), 9)
        self.assertEqual(len({row["id"] for row in results}), 9)
        self.assertEqual(len({row["declaration"] for row in results}), 9)
        for result in results:
            source = (ROOT / "research" / result["source"]).resolve()
            self.assertTrue(source.is_file())
            text = source.read_text()
            self.assertNotIn("sorry", text)
            self.assertNotIn("admit", text)
            self.assertIn(result["declaration"].rsplit(".", 1)[-1], text)

        record = next(
            item for item in inventory["formalizations"]
            if item["id"] == "lean4-normalized-simplex-boundary-bridge"
        )
        self.assertTrue(
            {row["declaration"] for row in results}.issubset(record["declarations"])
        )
        self.assertEqual(len(record["declarations"]), 59)
        self.assertEqual(record["commit"], "27e152aeca158e44b44d67197c045bb6d6d50345")
        self.assertIsNone(record["lattice_overlay"])
        self.assertIsNone(record["degree_lattice_overlay"])

    def test_stick_simplex_boundary_matches_sorry_free_sources(self) -> None:
        inventory = json.loads((ROOT / "research/formalizations.json").read_text())
        result_set = inventory["maintained_stick_simplex_boundary_set"]
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
            if item["id"] == "lean4-stick-simplex-boundary-shell"
        )
        self.assertTrue(
            {row["declaration"] for row in results}.issubset(record["declarations"])
        )
        self.assertEqual(len(record["declarations"]), 51)
        self.assertEqual(record["commit"], "b026de87c69de336d693d000377b930b8a95efad")
        self.assertIsNone(record["lattice_overlay"])
        self.assertIsNone(record["degree_lattice_overlay"])

    def test_supported_cubical_shell_matches_sorry_free_sources(self) -> None:
        inventory = json.loads((ROOT / "research/formalizations.json").read_text())
        result_set = inventory["maintained_supported_cubical_shell_set"]
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
            if item["id"] == "lean4-supported-cubical-shell-relations"
        )
        self.assertTrue(
            {row["declaration"] for row in results}.issubset(record["declarations"])
        )
        self.assertEqual(len(record["declarations"]), 52)
        self.assertEqual(record["commit"], "ae4d5507a8e6ee0ed2ad068c970a2afb10839796")
        self.assertIsNone(record["lattice_overlay"])
        self.assertIsNone(record["degree_lattice_overlay"])

    def test_simplex_horn_matches_sorry_free_sources(self) -> None:
        inventory = json.loads((ROOT / "research/formalizations.json").read_text())
        result_set = inventory["maintained_simplex_horn_set"]
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
            if item["id"] == "lean4-simplex-horn-attaching-homotopy"
        )
        self.assertTrue(
            {row["declaration"] for row in results}.issubset(record["declarations"])
        )
        self.assertEqual(len(record["declarations"]), 36)
        self.assertEqual(record["commit"], "fca23771175564ad4f46168b859f4c2d9af6a401")
        self.assertIsNone(record["lattice_overlay"])
        self.assertIsNone(record["degree_lattice_overlay"])

    def test_simplex_horn_regions_match_sorry_free_sources(self) -> None:
        inventory = json.loads((ROOT / "research/formalizations.json").read_text())
        result_set = inventory["maintained_simplex_horn_region_set"]
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
            if item["id"] == "lean4-simplex-horn-region-atlas"
        )
        self.assertTrue(
            {row["declaration"] for row in results}.issubset(record["declarations"])
        )
        self.assertEqual(len(record["declarations"]), 27)
        self.assertEqual(record["commit"], "210acde189e3b808a17ffe229256a0212a22cf29")
        self.assertIsNone(record["lattice_overlay"])
        self.assertIsNone(record["degree_lattice_overlay"])

    def test_singular_kan_matches_sorry_free_sources(self) -> None:
        inventory = json.loads((ROOT / "research/formalizations.json").read_text())
        result_set = inventory["maintained_singular_kan_set"]
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
            if item["id"] == "lean4-singular-simplicial-set-kan"
        )
        self.assertTrue(
            {row["declaration"] for row in results}.issubset(record["declarations"])
        )
        self.assertEqual(len(record["declarations"]), 21)
        self.assertEqual(record["commit"], "a26d9e13c8c3a5854dde7a563c98b0a07a666ed2")
        self.assertIsNone(record["lattice_overlay"])
        self.assertIsNone(record["degree_lattice_overlay"])

    def test_simplicial_addition_matches_sorry_free_sources(self) -> None:
        inventory = json.loads((ROOT / "research/formalizations.json").read_text())
        result_set = inventory["maintained_simplicial_addition_set"]
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
            if item["id"] == "lean4-simplicial-kan-multiplication"
        )
        self.assertTrue(
            {row["declaration"] for row in results}.issubset(record["declarations"])
        )
        self.assertEqual(len(record["declarations"]), 35)
        self.assertEqual(record["commit"], "4c48c6fce15bfc105c3dfdef36097501fd8a2149")
        self.assertIsNone(record["lattice_overlay"])
        self.assertIsNone(record["degree_lattice_overlay"])

    def test_simplicial_index_shifts_match_sorry_free_sources(self) -> None:
        inventory = json.loads((ROOT / "research/formalizations.json").read_text())
        result_set = inventory["maintained_simplicial_index_set"]
        results = result_set["results"]
        self.assertEqual(result_set["system"], "Lean 4")
        self.assertEqual(result_set["count"], 9)
        self.assertEqual(len(results), 9)
        self.assertEqual(len({row["id"] for row in results}), 9)
        self.assertEqual(len({row["declaration"] for row in results}), 9)
        for result in results:
            source = (ROOT / "research" / result["source"]).resolve()
            self.assertTrue(source.is_file())
            text = source.read_text()
            self.assertNotIn("sorry", text)
            self.assertNotIn("admit", text)
            self.assertIn(result["declaration"].rsplit(".", 1)[-1], text)

        records = {item["id"]: item for item in inventory["formalizations"]}
        index_record = records["lean4-simplicial-multiplication-index-shifts"]
        relation_record = records["lean4-final-simplicial-relation-invariance"]
        listed = set(index_record["declarations"]) | set(relation_record["declarations"])
        self.assertTrue({row["declaration"] for row in results}.issubset(listed))
        self.assertEqual(len(index_record["declarations"]), 35)
        self.assertEqual(
            index_record["commit"],
            "57508be42a5cdfee4b41a790d774d6ff375b8d19",
        )
        self.assertEqual(len(relation_record["declarations"]), 9)
        self.assertEqual(
            relation_record["commit"],
            "a80ebea79cf7c856c56419993dee7bf76b3a8235",
        )
        for record in (index_record, relation_record):
            self.assertIsNone(record["lattice_overlay"])
            self.assertIsNone(record["degree_lattice_overlay"])

    def test_simplicial_telescope_matches_sorry_free_source(self) -> None:
        inventory = json.loads((ROOT / "research/formalizations.json").read_text())
        result_set = inventory["maintained_simplicial_telescope_set"]
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
            if item["id"] == "lean4-simplicial-homotopy-addition-telescope"
        )
        self.assertTrue(
            {row["declaration"] for row in results}.issubset(record["declarations"])
        )
        self.assertEqual(len(record["declarations"]), 52)
        self.assertEqual(
            record["commit"],
            "e81934358c2157762e078d2ed7862ef6c1fef26c",
        )
        self.assertIsNone(record["lattice_overlay"])
        self.assertIsNone(record["degree_lattice_overlay"])

    def test_simplicial_descent_matches_sorry_free_sources(self) -> None:
        inventory = json.loads((ROOT / "research/formalizations.json").read_text())
        result_set = inventory["maintained_simplicial_descent_set"]
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
            if item["id"] == "lean4-simplicial-homotopy-class-descent"
        )
        self.assertTrue(
            {row["declaration"] for row in results}.issubset(record["declarations"])
        )
        self.assertEqual(len(record["declarations"]), 11)
        self.assertEqual(
            record["commit"],
            "5f82bb15772690852fd3723889ccb89a4542ee67",
        )
        self.assertIsNone(record["lattice_overlay"])
        self.assertIsNone(record["degree_lattice_overlay"])

    def test_absolute_hurewicz_surjectivity_matches_sorry_free_source(self) -> None:
        inventory = json.loads((ROOT / "research/formalizations.json").read_text())
        result_set = inventory["maintained_absolute_hurewicz_set"]
        results = result_set["results"]
        self.assertEqual(result_set["system"], "Lean 4")
        self.assertEqual(result_set["count"], 5)
        self.assertEqual(len(results), 5)
        self.assertEqual(len({row["id"] for row in results}), 5)
        self.assertEqual(len({row["declaration"] for row in results}), 5)
        for result in results:
            source = (ROOT / "research" / result["source"]).resolve()
            self.assertTrue(source.is_file())
            text = source.read_text()
            self.assertNotIn("sorry", text)
            self.assertNotIn("admit", text)
            self.assertIn(result["declaration"].rsplit(".", 1)[-1], text)

        record = next(
            item for item in inventory["formalizations"]
            if item["id"] == "lean4-first-absolute-hurewicz-surjectivity"
        )
        self.assertTrue(
            {row["declaration"] for row in results}.issubset(record["declarations"])
        )
        self.assertEqual(len(record["declarations"]), 8)
        self.assertEqual(
            record["commit"],
            "3b3d214c99369b2fd7b1ae2eb3c2483cd62dc937",
        )
        self.assertIsNone(record["lattice_overlay"])
        self.assertIsNone(record["degree_lattice_overlay"])

    def test_stick_sphere_coordinate_change_matches_sorry_free_sources(self) -> None:
        inventory = json.loads((ROOT / "research/formalizations.json").read_text())
        result_set = inventory["maintained_stick_sphere_coordinate_set"]
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
            if item["id"] == "lean4-stick-sphere-coordinate-change"
        )
        self.assertTrue(
            {row["declaration"] for row in results}.issubset(record["declarations"])
        )
        self.assertEqual(len(record["declarations"]), 26)
        self.assertEqual(
            record["commit"],
            "1984bff960ebd367faa093238ad898541e2f9493",
        )
        self.assertIsNone(record["lattice_overlay"])
        self.assertIsNone(record["degree_lattice_overlay"])

    def test_first_hurewicz_isomorphism_matches_sorry_free_sources(self) -> None:
        inventory = json.loads((ROOT / "research/formalizations.json").read_text())
        result_set = inventory["maintained_first_hurewicz_isomorphism_set"]
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
            if item["id"] == "lean4-first-nonvanishing-hurewicz-isomorphism"
        )
        self.assertTrue(
            {row["declaration"] for row in results}.issubset(record["declarations"])
        )
        self.assertEqual(len(record["declarations"]), 38)
        self.assertEqual(
            record["commit"],
            "a2578f3038f418a99d89b87691f2abdd60e7c2f2",
        )
        self.assertEqual(
            record["lattice_overlay"]["cell_ranges"],
            [{"n": [1, 92], "k": [0, 0]}],
        )
        self.assertEqual(
            record["lattice_overlay"]["proof"],
            {
                "declaration": "Submission.sphere_diagonal_homotopy_mulEquiv_int",
                "line": 34,
            },
        )
        generic = (
            ROOT
            / "examples/submissions/sphere_lower_homotopy_subsingleton/Submission/Hurewicz"
            / "SphereDiagonalGeneric.lean"
        )
        generic_text = generic.read_text()
        self.assertNotIn("sorry", generic_text)
        self.assertNotIn("admit", generic_text)
        spaces_text = (ROOT / "HomotopyGroups/Spaces.lean").read_text()
        start = spaces_text.index("theorem sphere_diagonal_homotopy_mulEquiv_int")
        end = spaces_text.index("\n@[eval_problem]", start)
        self.assertNotIn("sorry", spaces_text[start:end])
        self.assertIsNone(record["degree_lattice_overlay"])

    def test_real_projective_space_results_match_sorry_free_sources(self) -> None:
        inventory = json.loads((ROOT / "research/formalizations.json").read_text())
        record = next(
            item for item in inventory["formalizations"]
            if item["id"] == "lean4-real-projective-sphere-cover"
        )
        self.assertEqual(
            record["declarations"],
            [
                "HomotopyGroups.realProjectiveSpace_higher_homotopy_mulEquiv_sphere",
                "HomotopyGroups.pi1_realProjectiveSpace_mulEquiv_zmod_two",
            ],
        )
        self.assertEqual(
            record["commit"],
            "82a6ce0f1491a67af6336f0145f0a1178dadac0c",
        )
        wrapper = (ROOT / "research" / record["source"]).resolve()
        core = (
            ROOT
            / "examples/submissions/sphere_lower_homotopy_subsingleton/Submission"
            / "RealProjectiveSpace.lean"
        )
        core_text = core.read_text()
        self.assertNotIn("sorry", core_text)
        self.assertNotIn("admit", core_text)
        wrapper_text = wrapper.read_text()
        for declaration in record["declarations"]:
            marker = f"theorem {declaration.rsplit('.', 1)[-1]}"
            start = wrapper_text.index(marker)
            end = wrapper_text.find("\n@[eval_problem]", start)
            theorem_text = wrapper_text[start:] if end == -1 else wrapper_text[start:end]
            self.assertNotIn("sorry", theorem_text)
            self.assertNotIn("admit", theorem_text)
        self.assertIsNone(record["lattice_overlay"])
        self.assertIsNone(record["degree_lattice_overlay"])

    def test_canonical_foundations_match_sorry_free_sources(self) -> None:
        inventory = json.loads((ROOT / "research/formalizations.json").read_text())
        record = next(
            item for item in inventory["formalizations"]
            if item["id"] == "lean4-canonical-foundational-homotopy-api"
        )
        self.assertEqual(len(record["declarations"]), 10)
        self.assertEqual(
            record["commit"],
            "ac36ddfb165ae4b6e339886de473d2637445ef36",
        )
        wrapper = (ROOT / "research" / record["source"]).resolve()
        core = (
            ROOT
            / "examples/submissions/sphere_lower_homotopy_subsingleton/Submission"
            / "FoundationBenchmarks.lean"
        )
        for source in (wrapper, core):
            text = source.read_text()
            self.assertNotIn("sorry", text)
            self.assertNotIn("admit", text)
        wrapper_text = wrapper.read_text()
        for declaration in record["declarations"]:
            self.assertIn(f"theorem {declaration.rsplit('.', 1)[-1]}", wrapper_text)
        for problem_id in (
            "pi0_pathConnected_subsingleton",
            "pi1_simplyConnected_subsingleton",
            "higher_homotopy_mul_comm",
        ):
            self.assertIn(
                "knowledge_status=formalized_local",
                (ROOT / f"manifests/problems/{problem_id}.toml").read_text(),
            )
        self.assertIsNone(record["lattice_overlay"])
        self.assertIsNone(record["degree_lattice_overlay"])


if __name__ == "__main__":
    unittest.main()
