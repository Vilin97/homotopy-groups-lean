#!/usr/bin/env python3
"""Generate exact unstable groups from Thomeier's Satz 1.1-1.8.

``research/thomeier-unstable.json`` contains the compact, source-audited rule
registry.  This script combines those rules with the exact integral stable
groups in ``research/stable-stems.json`` and emits canonical browser data.
"""

from __future__ import annotations

import argparse
import copy
import json
import math
import pathlib
import sys
from typing import Any


ROOT = pathlib.Path(__file__).resolve().parent.parent
RULES_PATH = ROOT / "research" / "thomeier-unstable.json"
STABLE_PATH = ROOT / "research" / "stable-stems.json"
OUTPUT_PATH = ROOT / "website" / "public" / "data" / "thomeier-unstable.json"
ELIGIBLE_STEMS = tuple(range(21, 84)) + (87, 88, 89)
EXCLUDED_STEMS = (84, 85, 86, 90)
SOURCE_TITLES = {
    "iwx2023": "Stable homotopy groups of spheres: from dimension 0 to 90",
    "bix2025": "Classical Stable Homotopy Groups of Spheres via F_2-Synthetic Methods",
}


class RegistryError(ValueError):
    """Raised when the compact registry or derived records are inconsistent."""


def require(condition: bool, message: str) -> None:
    if not condition:
        raise RegistryError(message)


def is_power_of_two(value: int) -> bool:
    return value > 0 and value & (value - 1) == 0


def factor_prime_powers(order: int) -> dict[str, int]:
    """Factor one cyclic order into its primary cyclic factors."""

    require(order > 1, f"cyclic order must exceed one, got {order}")
    factors: dict[str, int] = {}
    remainder = order
    prime = 2
    while prime * prime <= remainder:
        power = 1
        while remainder % prime == 0:
            power *= prime
            remainder //= prime
        if power > 1:
            factors[str(prime)] = power
        prime += 1
    if remainder > 1:
        factors[str(remainder)] = remainder
    return factors


def canonical_invariant_factors(primary: dict[str, list[int]]) -> list[int]:
    """Combine primary cyclic summands into canonical invariant factors."""

    width = max((len(orders) for orders in primary.values()), default=0)
    result = [1] * width
    for orders in primary.values():
        padded = [1] * (width - len(orders)) + orders
        result = [left * right for left, right in zip(result, padded, strict=True)]
    return result


def direct_sum_group(
    stable_group: dict[str, Any], *, free_rank: int, cyclic_orders: list[int]
) -> dict[str, Any]:
    """Add the theorem's summands and return canonical group representations."""

    stable_integral = stable_group["integral_decomposition"]
    primary = copy.deepcopy(stable_group["primary_decomposition"])
    for order in cyclic_orders:
        for prime, prime_power in factor_prime_powers(order).items():
            primary.setdefault(prime, []).append(prime_power)
    primary = {
        prime: sorted(orders)
        for prime, orders in sorted(primary.items(), key=lambda item: int(item[0]))
    }
    factors = canonical_invariant_factors(primary)
    total_free_rank = stable_integral["free_rank"] + free_rank
    return {
        "primary_decomposition": primary,
        "integral_decomposition": {
            "free_rank": total_free_rank,
            "torsion_invariant_factors": factors,
        },
        "torsion_order": str(math.prod(factors)),
    }


def case_applies(case: dict[str, Any], quotient: int) -> bool:
    condition = case.get("when")
    if condition is None:
        return True
    if condition == "quotient_not_power_of_two":
        return not is_power_of_two(quotient)
    if condition == "quotient_at_least_two":
        return quotient >= 2
    raise RegistryError(f"unknown rule condition {condition!r}")


def prior_status(n: int, stem: int) -> str:
    if 21 <= stem <= 32:
        return "exact_2_primary_only"
    if stem == 33 and ((2 <= n <= 9) or (28 <= n <= 34)):
        return "exact_2_primary_only"
    if (n, stem) == (27, 33):
        return "source_conflict"
    return "integral_group_unclassified"


def load_json(path: pathlib.Path) -> dict[str, Any]:
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as error:
        raise RegistryError(f"failed to read {path}: {error}") from error
    require(isinstance(value, dict), f"{path}: root must be an object")
    return value


def build_payload() -> dict[str, Any]:
    registry = load_json(RULES_PATH)
    stable = load_json(STABLE_PATH)
    require(registry.get("schema_version") == "1.0.0", "unsupported rule schema")
    rules = registry.get("rules")
    require(isinstance(rules, list) and len(rules) == 8, "rules must cover 8 residues")
    require([rule.get("residue") for rule in rules] == list(range(8)),
            "rules must be ordered by residues 0 through 7")
    rules_by_residue = {rule["residue"]: rule for rule in rules}

    stable_rows = stable.get("stems")
    require(isinstance(stable_rows, list), "stable stems must be a list")
    stable_by_stem = {row["stem"]: row for row in stable_rows}
    for stem in ELIGIBLE_STEMS:
        require(stable_by_stem[stem].get("is_exact") is True,
                f"base stable stem {stem} is not exact")
    for stem in EXCLUDED_STEMS:
        require(stable_by_stem[stem].get("is_exact") is False,
                f"excluded stable stem {stem} unexpectedly became exact")

    stable_sources = {source["source_id"]: source for source in stable["sources"]}
    thomeier_sources = registry.get("sources")
    require(isinstance(thomeier_sources, list) and len(thomeier_sources) == 1,
            "registry must contain the Thomeier source")
    sources: list[dict[str, Any]] = []
    for source in list(stable["sources"]) + thomeier_sources:
        normalized_source = copy.deepcopy(source)
        source_id = normalized_source["source_id"]
        normalized_source.setdefault("title", SOURCE_TITLES.get(source_id))
        normalized_source.setdefault("publication_status", "published")
        require(isinstance(normalized_source.get("title"), str)
                and normalized_source["title"],
                f"source {source_id}: title must be nonempty")
        require(normalized_source["publication_status"] == "published",
                f"source {source_id}: unexpected publication status")
        sources.append(normalized_source)

    cells: list[dict[str, Any]] = []
    for stem in ELIGIBLE_STEMS:
        quotient, residue = divmod(stem, 8)
        rule = rules_by_residue[residue]
        cases = rule.get("cases")
        require(isinstance(cases, list), f"residue {residue}: cases must be a list")
        for case in cases:
            require(isinstance(case, dict), f"residue {residue}: case must be an object")
            if not case_applies(case, quotient):
                continue
            d = case.get("d")
            free_rank = case.get("free_rank")
            cyclic_orders = case.get("cyclic_orders")
            require(isinstance(d, int) and 1 <= d <= 7,
                    f"residue {residue}: invalid backward index")
            require(isinstance(free_rank, int) and free_rank >= 0,
                    f"residue {residue}, d={d}: invalid free rank")
            require(isinstance(cyclic_orders, list)
                    and all(isinstance(order, int) for order in cyclic_orders),
                    f"residue {residue}, d={d}: invalid cyclic orders")
            n = stem - d + 2
            m = 2 * stem - d + 2
            stable_row = stable_by_stem[stem]
            stable_refs = copy.deepcopy(stable_row["source_refs"])
            thomeier_ref = {
                "source_id": "thomeier1966",
                "locator": f"Satz {rule['theorem']}, journal p. {rule['journal_page']}",
                "scope": "integral unstable structure formula",
            }
            cells.append({
                "id": f"thomeier-r{stem}-d{d}",
                "stem": stem,
                "backward_index": d,
                "n": n,
                "m": m,
                "status": "exact_integral",
                "prior_status": prior_status(n, stem),
                "base_stable_stem": stem,
                "added_summands": {
                    "free_rank": free_rank,
                    "cyclic_orders": cyclic_orders,
                },
                "group": direct_sum_group(
                    stable_row["group"],
                    free_rank=free_rank,
                    cyclic_orders=cyclic_orders,
                ),
                "theorem": {
                    "number": rule["theorem"],
                    "journal_page": rule["journal_page"],
                    "formula_case": f"r congruent {residue} mod 8, d={d}",
                    "arithmetic_condition": case.get("when"),
                },
                "source_refs": stable_refs + [thomeier_ref],
            })

    cells.sort(key=lambda cell: (cell["stem"], cell["backward_index"]))
    expected_count = registry["scope"]["expected_record_count"]
    require(len(cells) == expected_count,
            f"derived {len(cells)} cells instead of {expected_count}")
    require(len({(cell["n"], cell["stem"]) for cell in cells}) == len(cells),
            "derived cells contain duplicate lattice coordinates")

    window = registry["scope"]["degree_window"]
    visible = [
        cell for cell in cells
        if window["n_min"] <= cell["n"] <= window["n_max"]
        and window["m_min"] <= cell["m"] <= window["m_max"]
    ]
    expected_visible = registry["scope"]["expected_degree_window_count"]
    require(len(visible) == expected_visible,
            f"derived {len(visible)} visible cells instead of {expected_visible}")

    def count_prior(rows: list[dict[str, Any]]) -> dict[str, int]:
        return {
            status: sum(row["prior_status"] == status for row in rows)
            for status in ("exact_2_primary_only", "integral_group_unclassified")
        }

    prior_all = count_prior(cells)
    prior_visible = count_prior(visible)
    expected_prior = registry["scope"]["expected_prior_status_counts"]
    require(prior_all == expected_prior["all_records"],
            f"all-record prior counts disagree: {prior_all}")
    require(prior_visible == expected_prior["degree_window"],
            f"degree-window prior counts disagree: {prior_visible}")

    used_source_ids = {
        ref["source_id"] for cell in cells for ref in cell["source_refs"]
    }
    source_ids = {source["source_id"] for source in sources}
    require(used_source_ids <= source_ids, "a cell references an unknown source")
    require(set(stable_sources) <= source_ids, "stable source metadata is incomplete")

    return {
        "schema_version": registry["schema_version"],
        "registry_version": registry["registry_version"],
        "reviewed_on": registry["reviewed_on"],
        "title": registry["title"],
        "coordinate": registry["coordinate"],
        "coverage": {
            "record_count": len(cells),
            "eligible_stems": list(ELIGIBLE_STEMS),
            "excluded_nonexact_stems": list(EXCLUDED_STEMS),
            "degree_window": window,
            "degree_window_count": len(visible),
            "prior_status_counts": {
                "all_records": prior_all,
                "degree_window": prior_visible,
            },
        },
        "sources": sources,
        "cells": cells,
    }


def render(payload: dict[str, Any]) -> str:
    return json.dumps(payload, indent=2, ensure_ascii=False) + "\n"


def parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true",
                        help="Fail if browser data differs from the audited registry.")
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    args = parse_args(argv)
    try:
        expected = render(build_payload())
    except RegistryError as error:
        print(f"Thomeier registry error: {error}", file=sys.stderr)
        return 2
    if args.check:
        try:
            actual = OUTPUT_PATH.read_text(encoding="utf-8")
        except OSError as error:
            print(f"cannot read {OUTPUT_PATH}: {error}", file=sys.stderr)
            return 1
        if actual != expected:
            print(f"stale {OUTPUT_PATH.relative_to(ROOT)}", file=sys.stderr)
            return 1
        print("Thomeier browser data are current (307 exact cells; 118 visible)")
        return 0
    OUTPUT_PATH.parent.mkdir(parents=True, exist_ok=True)
    if not OUTPUT_PATH.exists() or OUTPUT_PATH.read_text(encoding="utf-8") != expected:
        OUTPUT_PATH.write_text(expected, encoding="utf-8")
    print(f"generated {OUTPUT_PATH.relative_to(ROOT)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
