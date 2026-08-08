#!/usr/bin/env python3
"""Validate the 2026 handoff and generate the public extended-frontier atlas.

The files under ``research/comprehensive-handoff-2026`` are preserved byte for
byte.  This generator applies the repository's audited metadata corrections to
the normalized website registry without rewriting that source artifact.
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import html
import io
import json
import pathlib
import re
import sys
from collections import defaultdict
from typing import Any


ROOT = pathlib.Path(__file__).resolve().parent.parent
SOURCE = ROOT / "research" / "comprehensive-handoff-2026"
PUBLIC_REPORT = ROOT / "website" / "public" / "reports" / "comprehensive-2026"
PUBLIC_JSON = ROOT / "website" / "public" / "data" / "extended-frontiers.json"
ARCHIVE_SHA256 = "22e2f51ec60f14edf308845dc390475591608ba87f7d840fd11fd61d9b212e87"
CHECKSUMS_SHA256 = "41992cd04e5fab41be7456397040629f7c058e274717f7f59b33b3c5d51990ef"
KNOWLEDGE_CUTOFF = "2026-08-08"
RAVENEL_URL = (
    "https://www.sas.rochester.edu/mth/sites/doug-ravenel/mybooks/ravenel3rd.pdf"
)

CSV_FILES = (
    "computation_frontiers_2026.csv",
    "height_two_2_primary_192_periodic_families.csv",
    "high_dimensional_results_ledger.csv",
    "v1_periodic_image_J_0_1000.csv",
    "conjecture_status_ledger.csv",
    "unstable_computation_coverage.csv",
    "stable_stems_0_90.csv",
    "stable_5_primary_nonJ_0_999.csv",
    "source_ledger.csv",
    "stable_3_primary_groups_0_108.csv",
    "stable_3_primary_nonJ_classes_0_108.csv",
    "toda_unstable_stems_0_19.csv",
)

# Carrick--Davies Table 1 does not put a J_0(3) checkmark on these grouped
# rows.  Their 19 families are established by filtration arguments instead.
FILTRATION_ONLY_PERIODIC_ROWS = {
    (26, ""),
    (74, "a"),
    (74, "b"),
    (122, ""),
    (170, "a"),
    (170, "b"),
    (170, "c"),
}

# These rows contain page headers, detached superscript fragments, or broken
# operators introduced by the package's PDF-to-text extraction.  They are not
# question marks in Ravenel's source and must not be treated as source-level
# mathematical uncertainty.
P5_TRANSCRIPTION_QUARANTINE = {
    412, 475, 530, 601, 840, 875, 892, 954, 955, 964, 978, 990,
}


class GenerationError(ValueError):
    """Raised when the handoff violates its audited generation contract."""


def require(condition: bool, message: str) -> None:
    if not condition:
        raise GenerationError(message)


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def verify_handoff() -> None:
    checksum_path = SOURCE / "SHA256SUMS.txt"
    try:
        checksum_bytes = checksum_path.read_bytes()
        checksum_lines = checksum_bytes.decode("utf-8").splitlines()
    except OSError as exc:
        raise GenerationError(f"cannot read {checksum_path}: {exc}") from exc
    require(sha256(checksum_bytes) == CHECKSUMS_SHA256,
            "SHA256SUMS.txt does not match the received handoff")
    require(len(checksum_lines) == 16, "SHA256SUMS.txt must contain 16 payload entries")
    checksums: dict[str, str] = {}
    for line in checksum_lines:
        expected, relative = line.split(maxsplit=1)
        require(relative not in checksums, f"duplicate checksum path {relative}")
        require(not pathlib.PurePosixPath(relative).is_absolute() and
                ".." not in pathlib.PurePosixPath(relative).parts,
                f"unsafe checksum path {relative}")
        checksums[relative] = expected
        path = SOURCE / relative
        try:
            actual = sha256(path.read_bytes())
        except OSError as exc:
            raise GenerationError(f"cannot read handoff payload {relative}: {exc}") from exc
        require(actual == expected, f"handoff checksum mismatch for {relative}")

    try:
        manifest = json.loads((SOURCE / "MANIFEST.json").read_text(encoding="utf-8"))
    except (OSError, UnicodeError, json.JSONDecodeError) as exc:
        raise GenerationError(f"cannot parse handoff MANIFEST.json: {exc}") from exc
    require(manifest.get("package") == "homotopy_groups_spheres_formalization_handoff",
            "unexpected handoff package id")
    require(manifest.get("knowledge_cutoff") == KNOWLEDGE_CUTOFF,
            "handoff knowledge cutoff changed")
    manifest_files = manifest.get("files")
    require(isinstance(manifest_files, list) and len(manifest_files) == 15,
            "MANIFEST.json must describe 15 payload files")
    manifest_paths = {entry.get("path") for entry in manifest_files}
    require(manifest_paths == set(checksums) - {"MANIFEST.json"},
            "manifest and checksum payload path sets differ")
    for entry in manifest_files:
        relative = entry["path"]
        path = SOURCE / relative
        payload = path.read_bytes()
        require(len(payload) == entry["bytes"], f"manifest size mismatch for {relative}")
        require(sha256(payload) == entry["sha256"] == checksums[relative],
                f"manifest digest mismatch for {relative}")
        if "columns" not in entry:
            continue
        with path.open(encoding="utf-8", newline="") as handle:
            reader = csv.DictReader(handle)
            rows = list(reader)
        require(reader.fieldnames == entry["columns"],
                f"manifest CSV header mismatch for {relative}")
        require(len(rows) == entry["data_rows"],
                f"manifest CSV row-count mismatch for {relative}")
        row_keys = [tuple(row[column] for column in reader.fieldnames) for row in rows]
        duplicate_count = len(row_keys) - len(set(row_keys))
        require(duplicate_count == entry["duplicate_data_rows"],
                f"manifest CSV duplicate-count mismatch for {relative}")


def read_csv(name: str) -> list[dict[str, str]]:
    path = SOURCE / "data" / name
    try:
        with path.open(encoding="utf-8", newline="") as handle:
            return list(csv.DictReader(handle))
    except (OSError, csv.Error) as exc:
        raise GenerationError(f"cannot read {path}: {exc}") from exc


def contiguous(rows: list[dict[str, str]], field: str, first: int, last: int) -> bool:
    return [int(row[field]) for row in rows] == list(range(first, last + 1))


def normalized_source(text: str) -> str:
    # The handoff's A3.2 (3-primary) and A3.3 (5-primary) locators agree with
    # the 31 July 2026 third-edition PDF.  Keep those table numbers intact.
    return text


def build_registry() -> dict[str, Any]:
    verify_handoff()
    integral = read_csv("stable_stems_0_90.csv")
    three = read_csv("stable_3_primary_groups_0_108.csv")
    five = read_csv("stable_5_primary_nonJ_0_999.csv")
    image_j = read_csv("v1_periodic_image_J_0_1000.csv")
    periodic = read_csv("height_two_2_primary_192_periodic_families.csv")
    frontiers = read_csv("computation_frontiers_2026.csv")
    high_dimensional = read_csv("high_dimensional_results_ledger.csv")
    conjectures = read_csv("conjecture_status_ledger.csv")
    source_ledger = read_csv("source_ledger.csv")

    require(len(integral) == 91 and contiguous(integral, "stem", 0, 90),
            "integral ledger must be contiguous from 0 through 90")
    require(len(three) == 109 and contiguous(three, "stem", 0, 108),
            "3-primary ledger must be contiguous from 0 through 108")
    require(all(row["status"] == "exact" for row in three),
            "every 3-primary group row must be exact")
    require(len(five) == 354, "5-primary non-J ledger must have 354 occupied rows")
    require(len({int(row["stem"]) for row in five}) == len(five),
            "5-primary non-J stems must be unique")
    require(max(int(row["stem"]) for row in five) == 999,
            "5-primary non-J ledger must end at stem 999")
    uncertain_five = sorted(
        int(row["stem"]) for row in five if row["contains_source_question_mark"] == "yes"
    )
    require(uncertain_five == [932, 933, 970, 971],
            "unexpected 5-primary source-question-mark stems")
    five_stems = {int(row["stem"]) for row in five}
    require(P5_TRANSCRIPTION_QUARANTINE <= five_stems,
            "a quarantined 5-primary transcription stem is missing")
    require(not (P5_TRANSCRIPTION_QUARANTINE & set(uncertain_five)),
            "package transcription defects must remain distinct from source question marks")
    require(len(image_j) == 1520, "image-J/v1 ledger must have 1,520 rows")
    require(min(int(row["stem"]) for row in image_j) == 0 and
            max(int(row["stem"]) for row in image_j) == 1000,
            "image-J/v1 ledger must span stems 0 through 1000")
    require(len(periodic) == 26, "height-two ledger must have 26 grouped rows")
    require(sum(int(row["number_of_families_in_row"]) for row in periodic) == 125,
            "height-two ledger must represent 125 families")
    residues = sorted({int(row["residue_mod_192"]) for row in periodic})
    require(len(residues) == 19, "height-two ledger must use 19 residues")
    require(len(frontiers) == 14, "frontier ledger must have 14 rows")
    require(len(high_dimensional) == 22, "high-dimensional result ledger must have 22 rows")
    require(len(conjectures) == 27, "conjecture status ledger must have 27 rows")
    require(len(source_ledger) == 128, "source ledger must have 128 rows")
    require(sum(not row["url"] for row in source_ledger) == 115,
            "source-ledger URL completeness changed; re-audit required")
    require(sum(not row["doi"] for row in source_ledger) == 125,
            "source-ledger DOI completeness changed; re-audit required")

    integral_rows = [
        {
            "stem": int(row["stem"]),
            "group": row["total_additive_group"],
            "status": (
                "exact" if row["status"].startswith("exact")
                else "published_alternatives"
            ),
            "source_status": row["status"],
        }
        for row in integral
    ]
    three_rows = [
        {
            "stem": int(row["stem"]),
            "group": row["full_3_primary_component"],
            "image_j_or_degree_zero": row["image_J_or_degree_zero"],
            "non_j_component": row["non_J_component"],
            "non_j_generators": row["non_J_generators"],
            "notes": row["notes"],
            "nonzero": row["full_3_primary_component"] != "0",
            "scope": (
                "3_local_degree_zero" if int(row["stem"]) == 0
                else "3_primary_torsion_component"
            ),
            "source": normalized_source(row["source"]),
        }
        for row in three
    ]
    five_rows = [
        {
            "stem": int(row["stem"]),
            "transcription": row["non_J_elements_and_relations_source_transcription"],
            "uncertain": row["contains_source_question_mark"] == "yes",
            "quarantined": int(row["stem"]) in P5_TRANSCRIPTION_QUARANTINE,
            "transcription_status": (
                "source_uncertain" if row["contains_source_question_mark"] == "yes" else
                "package_extraction_defect" if int(row["stem"]) in P5_TRANSCRIPTION_QUARANTINE else
                "transcribed"
            ),
            "source": normalized_source(row["source"]),
            "source_url": RAVENEL_URL,
        }
        for row in five
    ]

    image_by_stem: dict[int, list[dict[str, str]]] = defaultdict(list)
    corrected_v1_rows = 0
    for row in image_j:
        group = row["group"]
        if (row["stem"], row["prime"], row["family_type"], group) == (
            "3", "2", "2-primary v1-periodic", "Z/4"
        ):
            # The source artifact's low-dimensional exception contradicts both
            # pi_3^S = Z/24 and the cited v1-periodic formula.  Its 2-part is C8.
            group = "Z/8"
            corrected_v1_rows += 1
        image_by_stem[int(row["stem"])].append(
            {
                "prime": row["prime"],
                "family_type": row["family_type"],
                "group": group,
                "formula_case": row["formula_case"],
                "status": row["status"],
            }
        )
    require(corrected_v1_rows == 1, "expected exactly one low-dimensional v1 correction")

    periodic_by_residue: dict[int, list[dict[str, Any]]] = defaultdict(list)
    corrected_periodic_family_count = 0
    for row in periodic:
        residue = int(row["residue_mod_192"])
        key = (residue, row["row_label"])
        filtration_only = key in FILTRATION_ONLY_PERIODIC_ROWS
        if filtration_only:
            corrected_periodic_family_count += int(row["number_of_families_in_row"])
        periodic_by_residue[residue].append(
            {
                "row_label": row["row_label"],
                "cyclic_order": row["cyclic_order"],
                "representative": row["representative_notation"],
                "filtration_range": row["filtration_range_as_source"],
                "family_count": int(row["number_of_families_in_row"]),
                "proof_method": (
                    "nonvanishing via the filtration argument of Theorem 5.1; T(2)/K(2)-local nonzero by Remark 5.5; J₀(3) detection is not certified by Table 1"
                    if filtration_only else
                    "detected by the Atkin–Lehner fixed-point spectrum J₀(3); T(2)/K(2)-local nonzero by Remark 5.5"
                ),
                "source": row["source"],
                "source_url": row["source_url"],
            }
        )
    require(corrected_periodic_family_count == 19,
            "detector correction must cover exactly 19 periodic families")

    normalized_frontiers: list[dict[str, str]] = []
    for row in frontiers:
        normalized = dict(row)
        normalized["principal_source"] = normalized_source(normalized["principal_source"])
        if row["object"] == "2-primary unstable 33-stem":
            normalized["principal_source"] = (
                "Yang-Wu arXiv:2406.08621v5 (2024 preprint) and published predecessors"
            )
        normalized_frontiers.append(normalized)

    normalized_high_dimensional: list[dict[str, str]] = []
    for row in high_dimensional:
        normalized = dict(row)
        normalized["source"] = normalized_source(normalized["source"])
        if normalized["source"].startswith("Ravenel 2026"):
            normalized["status"] = normalized["status"].replace(
                "published digital monograph", "author-maintained digital monograph revision"
            ).replace("theorem in 2026 monograph", "theorem in author-maintained 2026 revision")
        if "Bhattacharya-Bobkova-Quigley" in normalized["source"]:
            normalized["status"] = "peer-reviewed publication (Geometry & Topology, 2026)"
            normalized["source"] = (
                "Bhattacharya-Bobkova-Quigley, Geometry & Topology 30 (2026), "
                "2367–2393, DOI 10.2140/gt.2026.30.2367"
            )
        if "Carrick-Davies, arXiv:2410.02564v3" in normalized["source"]:
            normalized["status"] = "accepted / forthcoming Advances in Mathematics"
        if "Guchuan Li-Yunze Li" in normalized["source"]:
            normalized["source"] = (
                "Runji Li and Yuxuan Li, Proceedings of the AMS, DOI 10.1090/proc/17823"
            )
        if normalized["data_type"] == "partial unstable stem":
            normalized["status"] = (
                "broader three-group source is a 2024 preprint; published predecessor components"
            )
            normalized["source"] = "Yang-Wu, arXiv:2406.08621v5, and published predecessors"
        normalized_high_dimensional.append(normalized)

    normalized_conjectures: list[dict[str, str]] = []
    conjecture_correction_counts = {
        "ravenel_urls": 0,
        "new_doomsday": 0,
        "lannes_zarati": 0,
        "ehp_index": 0,
        "beta_bracket": 0,
        "weak_splitting": 0,
        "moore": 0,
    }
    for row in conjectures:
        normalized = {
            "name": row["name"],
            "area": row["area"],
            "statement": row["statement"],
            "status": row["status_2026"],
            "evidence": row["credibility_or_evidence"],
            "source": row["source"],
            "source_url": row["source_url"],
        }
        if normalized["source_url"].endswith("/mybooks/ravenel.pdf"):
            normalized["source_url"] = RAVENEL_URL
            conjecture_correction_counts["ravenel_urls"] += 1
        if normalized["name"] == "New Doomsday conjecture":
            normalized["statement"] = (
                "For every Adams filtration s there is an n(s) such that no nonzero "
                "class in the image of (Sq^0)^(n(s)) in the mod-two Adams E_2-page "
                "at filtration s is a permanent cycle."
            )
            normalized["source"] = "Minami 1995; progress by Burklund-Xu and Li-Li"
            normalized["source_url"] = "https://doi.org/10.2307/2374955"
            conjecture_correction_counts["new_doomsday"] += 1
        if normalized["name"].startswith("Lannes-Zarati"):
            normalized["source_url"] = "https://doi.org/10.1016/j.crma.2014.01.013"
            conjecture_correction_counts["lannes_zarati"] += 1
        if normalized["name"].startswith("Ravenel EHP differential"):
            normalized["statement"] = normalized["statement"].replace(
                "d_{2^j-2}(nu)", "d_{2^{j-2}}(nu)"
            )
            normalized["source_url"] = RAVENEL_URL
            conjecture_correction_counts["ehp_index"] += 1
        if normalized["name"].startswith("Ravenel beta_1 exponent"):
            normalized["statement"] = (
                "For p>=7, beta_1^(p^2-p) is nonzero, beta_1^(p^2-p+1) vanishes, "
                "and <gamma_3,gamma_2,...,gamma_2>, with gamma_2 repeated "
                "(p-5)/2 times, equals beta_1^((2p-1)(p-1)/2)."
            )
            conjecture_correction_counts["beta_bracket"] += 1
        if normalized["name"] == "Chromatic splitting conjecture - weak form":
            normalized["statement"] = (
                "For every prime p, height n>=1, and finite spectrum X, L_(n-1) "
                "of the p-completion of X is a wedge summand of L_(n-1)L_K(n) "
                "of the p-completion of X."
            )
            normalized["source"] = "Hovey 1995, Introduction p. 2 and Conjecture 4.2(v)"
            normalized["source_url"] = "https://doi.org/10.1090/conm/181/02036"
            conjecture_correction_counts["weak_splitting"] += 1
        if normalized["name"].startswith("Moore conjecture"):
            normalized["source_url"] = "https://doi.org/10.1017/S0305004100060916"
            conjecture_correction_counts["moore"] += 1
        normalized_conjectures.append(normalized)
    require(
        conjecture_correction_counts == {
            "ravenel_urls": 7,
            "new_doomsday": 1,
            "lannes_zarati": 1,
            "ehp_index": 1,
            "beta_bracket": 1,
            "weak_splitting": 1,
            "moore": 1,
        },
        "unexpected conjecture-ledger correction count",
    )

    return {
        "schema_version": "1.0.0",
        "knowledge_cutoff": KNOWLEDGE_CUTOFF,
        "source_archive_sha256": ARCHIVE_SHA256,
        "display": {"first_stem": 0, "last_stem": 1000},
        "interpretive_rule": (
            "Coverage, a named class, and a complete integral group are different claims."
        ),
        "audit_corrections": [
            {
                "id": "ravenel-edition-link",
                "source_artifact": "The handoff links an older ravenel.pdf revision.",
                "normalized": (
                    "Consumers link the 31 July 2026 third-edition PDF. Its table "
                    "locators agree with the handoff: A3.2 for 3-primary, A3.3 for "
                    "5-primary, and A3.4 for Toda's unstable table."
                ),
                "source_url": RAVENEL_URL,
            },
            {
                "id": "periodic-family-detectors",
                "source_artifact": "All 26 grouped rows carry one blanket J_0(3)/T(2)/K(2) detector label.",
                "normalized": (
                    "Rows 26, 74a, 74b, 122, 170a, 170b, and 170c—19 families—"
                    "are labeled as filtration arguments rather than J₀(3)-detected."
                ),
                "source_url": "https://arxiv.org/abs/2506.20507",
            },
            {
                "id": "low-dimensional-v1-exception",
                "source_artifact": "The instantiated ledger gives Z/4 at stem 3 and p=2.",
                "normalized": (
                    "Corrected to Z/8, the 2-primary part of pi_3^S = Z/24 and the "
                    "low-dimensional value required by the cited v1-periodic computation."
                ),
                "source_url": "https://arxiv.org/abs/2001.04247",
            },
            {
                "id": "yang-wu-publication-status",
                "source_artifact": (
                    "The source ledger assigns the three-group paper to HHA 28(1), "
                    "67–97 (2026)."
                ),
                "normalized": (
                    "The three-group paper is treated as arXiv:2406.08621v5 (2024 preprint); "
                    "that HHA slot belongs to an unrelated paper. The narrower S^6 result "
                    "appears in HHA 27(2) (2025), 53–60."
                ),
                "source_url": "https://arxiv.org/abs/2406.08621",
            },
            {
                "id": "p5-transcription-quarantine",
                "source_artifact": (
                    "Twelve p=5 CSV rows contain detached fragments, page headers, or "
                    "broken operators introduced by text extraction."
                ),
                "normalized": (
                    "Stems 412, 475, 530, 601, 840, 875, 892, 954, 955, 964, "
                    "978, and 990 are quarantined pending a checked transcription of "
                    "Table A3.3; this is separate from the source question marks."
                ),
                "source_url": RAVENEL_URL,
            },
            {
                "id": "publication-metadata",
                "source_artifact": (
                    "The high-dimensional ledger has stale or incorrect status metadata "
                    "for BBQ, the p=3 Carrick–Davies paper, the e-family paper, and Ravenel."
                ),
                "normalized": (
                    "BBQ is published in Geometry & Topology; Carrick–Davies p=3 is "
                    "accepted for Advances in Mathematics; the e-family authors are Runji "
                    "Li and Yuxuan Li; Ravenel is an author-maintained July 2026 revision."
                ),
                "source_url": "https://doi.org/10.2140/gt.2026.30.2367",
            },
            {
                "id": "source-ledger-deduplication",
                "source_artifact": "The 128-row source ledger contains duplicate works and duplicate bibkeys.",
                "normalized": (
                    "Generated consumers do not key directly from this raw ledger; it is "
                    "classified as a provenance inventory requiring deduplication."
                ),
                "source_url": "https://github.com/Vilin97/homotopy-groups-lean/blob/main/research/comprehensive-handoff-audit.md",
            },
            {
                "id": "conjecture-ledger-citations-and-ehp-index",
                "source_artifact": (
                    "The conjecture ledger has incorrect Lannes–Zarati and Moore DOI "
                    "links, points Ravenel entries at an older revision, leaves New "
                    "Doomsday and weak chromatic splitting without their original "
                    "anchors, and prints the EHP differential subscript as 2^j-2."
                ),
                "normalized": (
                    "Consumers use DOI 10.1016/j.crma.2014.01.013 for Lannes–Zarati, "
                    "DOI 10.1017/S0305004100060916 for Moore, Minami's 1995 "
                    "New Doomsday statement, Hovey's 1995 weak splitting statement, "
                    "Ravenel's current revision, and the directly verified "
                    "differential d_{2^{j-2}}(nu)=eta_j."
                ),
                "source_url": RAVENEL_URL,
            },
        ],
        "integral": {
            "claim_type": "complete_integral_additive_group",
            "coverage": {"first": 0, "last": 90},
            "exact_through": 83,
            "exact_again": [87, 88, 89],
            "published_alternative_stems": [84, 85, 86, 90],
            "stems": integral_rows,
        },
        "three_primary": {
            "claim_type": "degree_zero_3_local_plus_complete_positive_3_primary_components",
            "coverage": {
                "degree_zero": {"stem": 0, "scope": "3_localization", "status": "exact"},
                "positive_stem_primary_components": {
                    "first": 1, "last": 108, "status": "exact"
                },
            },
            "stems": three_rows,
        },
        "five_primary_non_j": {
            "claim_type": "named_non_J_class_and_relation_ledger",
            "coverage": {"first": 0, "last": 999},
            "entry_count": len(five_rows),
            "uncertain_stems": uncertain_five,
            "quarantined_transcription_stems": sorted(P5_TRANSCRIPTION_QUARANTINE),
            "missing_row_meaning": "no non-J entry is listed; it does not assert a zero group",
            "machine_readiness": (
                "class/relation metadata only; flattened notation and quarantined rows "
                "are not a machine-ready additive-group table"
            ),
            "entries": five_rows,
        },
        "image_j_v1": {
            "claim_type": "closed_height_one_formula",
            "theorem_scope": "all_stems",
            "ledger": {"first": 0, "last": 1000, "row_count": len(image_j)},
            "occupied_stem_count": len(image_by_stem),
            "stems": [
                {"stem": stem, "entries": entries}
                for stem, entries in sorted(image_by_stem.items())
            ],
        },
        "height_two_two_primary": {
            "claim_type": "periodic_class_existence_not_ambient_group_classification",
            "period": 192,
            "family_count": 125,
            "grouped_row_count": 26,
            "residue_count": len(residues),
            "residues": [
                {
                    "residue": residue,
                    "family_count": sum(row["family_count"] for row in rows),
                    "rows": rows,
                }
                for residue, rows in sorted(periodic_by_residue.items())
            ],
        },
        "frontiers": normalized_frontiers,
        "high_dimensional_results": normalized_high_dimensional,
        "source_ledger_status": {
            "row_count": len(source_ledger),
            "blank_url_count": sum(not row["url"] for row in source_ledger),
            "blank_doi_count": sum(not row["doi"] for row in source_ledger),
            "duplicate_bibkeys": ["BurklundHahnLevySchlank2023", "BurklundIsaksenXu2025"],
            "duplicate_work_pair_count": 11,
            "machine_status": "raw provenance inventory requiring deduplication",
        },
        "conjecture_status": {
            "record_count": len(conjectures),
            "entries": normalized_conjectures,
        },
    }


def render_inline(text: str) -> str:
    text = re.sub(r"\\([_*<>\[\]])", r"\1", text)
    rendered = html.escape(text, quote=True)
    rendered = re.sub(
        r"\[([^\]]+)\]\((https?://[^)]+)\)",
        lambda match: (
            f'<a href="{match.group(2)}" rel="noreferrer">{match.group(1)}</a>'
        ),
        rendered,
    )
    rendered = re.sub(r"`([^`]+)`", r"<code>\1</code>", rendered)
    rendered = re.sub(r"\*\*([^*]+)\*\*", r"<strong>\1</strong>", rendered)
    rendered = re.sub(r"(?<!\*)\*([^*]+)\*(?!\*)", r"<em>\1</em>", rendered)
    return rendered


def slug(text: str, used: set[str]) -> str:
    value = re.sub(r"[^a-z0-9]+", "-", text.lower()).strip("-") or "section"
    base = value
    index = 2
    while value in used:
        value = f"{base}-{index}"
        index += 1
    used.add(value)
    return value


def is_table_rule(line: str) -> bool:
    cells = [cell.strip() for cell in line.strip().strip("|").split("|")]
    return bool(cells) and all(re.fullmatch(r":?-{3,}:?", cell) for cell in cells)


def pipe_cells(line: str) -> list[str]:
    return [cell.strip() for cell in line.strip().strip("|").split("|")]


def render_markdown(markdown: str) -> tuple[str, list[tuple[int, str, str]]]:
    lines = markdown.splitlines()
    output: list[str] = []
    headings: list[tuple[int, str, str]] = []
    used_slugs: set[str] = set()
    index = 0
    while index < len(lines):
        line = lines[index]
        if not line.strip():
            index += 1
            continue
        heading = re.match(r"^(#{1,3})\s+(.+)$", line)
        if heading:
            level = len(heading.group(1))
            title = heading.group(2).strip()
            # The source artifact accidentally repeats two heading titles after
            # a second Markdown marker.  Keep the raw report unchanged while
            # avoiding duplicate navigation labels in the rendered edition.
            title = title.split("##", 1)[0].strip()
            anchor = slug(title, used_slugs)
            headings.append((level, title, anchor))
            output.append(f'<h{level} id="{anchor}">{render_inline(title)}</h{level}>')
            index += 1
            continue
        if line.lstrip().startswith("<table"):
            raw: list[str] = []
            while index < len(lines):
                raw.append(lines[index])
                index += 1
                if "</table>" in raw[-1]:
                    break
            note = re.sub(r"<br\s*/?>", " — ", "\n".join(raw), flags=re.I)
            note = re.sub(r"<[^>]+>", " ", note)
            note = html.unescape(re.sub(r"\s+", " ", note)).strip()
            if note:
                output.append(f'<aside class="report-note">{render_inline(note)}</aside>')
            continue
        if line.startswith("|") and index + 1 < len(lines) and is_table_rule(lines[index + 1]):
            header = pipe_cells(line)
            index += 2
            body: list[list[str]] = []
            while index < len(lines) and lines[index].startswith("|"):
                body.append(pipe_cells(lines[index]))
                index += 1
            output.append('<div class="table-scroll"><table><thead><tr>')
            output.extend(f"<th>{render_inline(cell)}</th>" for cell in header)
            output.append("</tr></thead><tbody>")
            for row in body:
                output.append("<tr>")
                output.extend(f"<td>{render_inline(cell)}</td>" for cell in row)
                output.append("</tr>")
            output.append("</tbody></table></div>")
            continue
        if line.startswith("- "):
            items: list[str] = []
            while index < len(lines) and lines[index].startswith("- "):
                items.append(lines[index][2:].strip())
                index += 1
                while index < len(lines) and lines[index].startswith("  "):
                    items[-1] += " " + lines[index].strip()
                    index += 1
            output.append("<ul>" + "".join(f"<li>{render_inline(item)}</li>" for item in items) + "</ul>")
            continue
        if re.match(r"^\d+\.\s", line):
            items = []
            while index < len(lines) and re.match(r"^\d+\.\s", lines[index]):
                items.append(re.sub(r"^\d+\.\s+", "", lines[index]))
                index += 1
                while index < len(lines) and lines[index].startswith("  "):
                    items[-1] += " " + lines[index].strip()
                    index += 1
            output.append("<ol>" + "".join(f"<li>{render_inline(item)}</li>" for item in items) + "</ol>")
            continue
        if line.startswith(">"):
            quote: list[str] = []
            while index < len(lines) and lines[index].startswith(">"):
                quote.append(lines[index].lstrip("> "))
                index += 1
            output.append(f"<blockquote>{render_inline(' '.join(quote))}</blockquote>")
            continue
        paragraph = [line.strip()]
        index += 1
        while index < len(lines) and lines[index].strip():
            candidate = lines[index]
            if (re.match(r"^#{1,3}\s", candidate) or candidate.startswith(("- ", ">", "|", "<table"))
                    or re.match(r"^\d+\.\s", candidate)):
                break
            paragraph.append(candidate.strip())
            index += 1
        output.append(f"<p>{render_inline(' '.join(paragraph))}</p>")
    return "\n".join(output), headings


def render_report_html(markdown: str) -> str:
    article, headings = render_markdown(markdown)
    toc = "".join(
        f'<a class="level-{level}" href="#{anchor}">{html.escape(title)}</a>'
        for level, title, anchor in headings if level <= 2
    )
    downloads = "".join(
        f'<a href="data/{name}">{html.escape(name.replace("_", " "))}</a>'
        for name in CSV_FILES
    )
    return f"""<!doctype html>
<html lang="en"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<title>Comprehensive 2026 report · Homotopy Groups Lean</title>
<meta name="description" content="Formalization-oriented survey and audited data ledgers for homotopy groups of spheres through August 2026.">
<style>
:root{{--bg:#090c11;--panel:#0f141c;--text:#f3f0e8;--muted:#9aa6b6;--line:#293240;--green:#4fdda8;--amber:#ffb75e;--blue:#8fb6ff}}*{{box-sizing:border-box}}html{{scroll-behavior:smooth;background:var(--bg)}}body{{margin:0;background:var(--bg);color:var(--text);font:16px/1.7 ui-sans-serif,system-ui,sans-serif}}a{{color:var(--blue)}}.top{{position:sticky;top:0;z-index:3;display:flex;justify-content:space-between;gap:20px;padding:14px clamp(18px,4vw,64px);border-bottom:1px solid var(--line);background:rgba(9,12,17,.94);backdrop-filter:blur(15px)}}.top a{{font:12px ui-monospace,monospace;text-decoration:none}}.layout{{display:grid;grid-template-columns:280px minmax(0,900px);gap:48px;justify-content:center;padding:48px 24px 100px}}nav{{position:sticky;top:86px;max-height:calc(100vh - 110px);overflow:auto;padding-right:18px}}nav a{{display:block;padding:5px 0;color:var(--muted);font:10px/1.4 ui-monospace,monospace;text-decoration:none}}nav a.level-1{{margin-top:11px;color:var(--green);font-weight:700}}nav a.level-2{{padding-left:12px}}article{{min-width:0}}h1,h2,h3{{scroll-margin-top:90px;line-height:1.08;letter-spacing:-.035em}}h1{{margin:0 0 28px;font-size:clamp(42px,6vw,74px)}}h2{{margin:70px 0 18px;padding-top:26px;border-top:1px solid var(--line);font-size:34px}}h3{{margin:40px 0 14px;font-size:23px}}p,li{{color:#c3cad4}}code{{padding:2px 5px;border:1px solid var(--line);background:var(--panel);font:13px ui-monospace,monospace}}blockquote,.report-note{{margin:24px 0;padding:18px 20px;border-left:3px solid var(--amber);background:var(--panel);color:#d8dde4}}.audit{{margin:0 0 34px;padding:18px 20px;border:1px solid rgba(255,183,94,.55);background:rgba(255,183,94,.07)}}.audit strong{{color:var(--amber)}}.downloads{{display:grid;grid-template-columns:repeat(auto-fit,minmax(210px,1fr));gap:7px;margin:24px 0 44px}}.downloads a{{overflow:hidden;padding:9px 11px;border:1px solid var(--line);background:var(--panel);font:10px ui-monospace,monospace;text-overflow:ellipsis;white-space:nowrap}}.table-scroll{{overflow:auto;margin:24px 0;border:1px solid var(--line)}}table{{width:100%;border-collapse:collapse;font-size:13px}}th,td{{min-width:120px;padding:10px 12px;border-right:1px solid var(--line);border-bottom:1px solid var(--line);text-align:left;vertical-align:top}}th{{position:sticky;top:0;background:#151b25;color:var(--green);font:10px ui-monospace,monospace;text-transform:uppercase}}ul,ol{{padding-left:24px}}@media(max-width:900px){{.layout{{display:block;padding-inline:16px}}nav{{position:static;max-height:280px;margin-bottom:42px;padding:15px;border:1px solid var(--line)}}}}
</style></head><body>
<header class="top"><a href="../../">← Homotopy Groups Lean</a><a href="REPORT_CORE.md">raw Markdown</a></header>
<div class="layout"><nav aria-label="Report contents">{toc}</nav><article>
<aside class="audit"><strong>Repository audit overlay.</strong> The attached artifact is preserved verbatim. Generated consumers update the Ravenel edition link, correct the stem-3 2-primary v₁ entry to Z/8, split seven grouped period-192 detector labels, remove unsupported Yang–Wu journal metadata, and repair audited conjecture-ledger citations. <a href="https://github.com/Vilin97/homotopy-groups-lean/blob/main/research/comprehensive-handoff-audit.md">Read the correction log.</a></aside>
<section class="downloads" aria-label="Report downloads">{downloads}</section>{article}
</article></div></body></html>"""


def desired_outputs() -> dict[pathlib.Path, bytes]:
    registry = build_registry()
    report_markdown = (SOURCE / "REPORT_CORE.md").read_text(encoding="utf-8")
    outputs: dict[pathlib.Path, bytes] = {
        PUBLIC_JSON: (json.dumps(registry, indent=2, sort_keys=True, ensure_ascii=False) + "\n").encode(),
        PUBLIC_REPORT / "index.html": render_report_html(report_markdown).encode(),
    }
    for name in ("REPORT_CORE.md", "FORMALIZATION_GUIDE.md", "README.md", "MANIFEST.json", "SHA256SUMS.txt"):
        outputs[PUBLIC_REPORT / name] = (SOURCE / name).read_bytes()
    for name in CSV_FILES:
        outputs[PUBLIC_REPORT / "data" / name] = (SOURCE / "data" / name).read_bytes()
    return outputs


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args(argv)
    try:
        outputs = desired_outputs()
    except (GenerationError, OSError, UnicodeError, json.JSONDecodeError) as exc:
        print(f"extended-frontier generation failed: {exc}", file=sys.stderr)
        return 2
    stale: list[str] = []
    for path, expected in outputs.items():
        if args.check:
            try:
                actual = path.read_bytes()
            except OSError:
                actual = b""
            if actual != expected:
                stale.append(str(path.relative_to(ROOT)))
        else:
            path.parent.mkdir(parents=True, exist_ok=True)
            if not path.exists() or path.read_bytes() != expected:
                path.write_bytes(expected)
    if args.check:
        expected_report_files = {
            path for path in outputs if path.is_relative_to(PUBLIC_REPORT)
        }
        actual_report_files = (
            {path for path in PUBLIC_REPORT.rglob("*") if path.is_file()}
            if PUBLIC_REPORT.exists() else set()
        )
        stale.extend(
            str(path.relative_to(ROOT))
            for path in sorted(actual_report_files - expected_report_files)
        )
    if stale:
        print("stale generated extended-frontier files: " + ", ".join(stale), file=sys.stderr)
        return 1
    print(f"extended-frontier data {'current' if args.check else 'generated'} ({len(outputs)} files)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
