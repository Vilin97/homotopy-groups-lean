#!/usr/bin/env python3
"""Generate exact low-stem groups displayed by the website lattice.

The source tables use compact direct-sum notation.  This generator normalizes
every group to canonical invariant factors and attaches cell-level provenance.
"""

from __future__ import annotations

import argparse
import csv
import json
import math
import pathlib
import re
import sys
from typing import Any


ROOT = pathlib.Path(__file__).resolve().parents[1]
TODA_PATH = ROOT / "research/report-data/toda_unstable_stems_0_19.csv"
MIMURA_TODA_PATH = ROOT / "research/report-data/mimura_toda_unstable_stem_20.csv"
OUTPUT_PATH = ROOT / "website/public/data/low-stem-exact.json"
FACTOR_RE = re.compile(r"(infty|[1-9][0-9]*)(?:\^([1-9][0-9]*))?\Z")


class RegistryError(ValueError):
    """Raised when a low-stem source row violates the registry contract."""


def require(condition: bool, message: str) -> None:
    if not condition:
        raise RegistryError(message)


def factor_order(order: int) -> dict[int, int]:
    require(order > 1, f"cyclic order must exceed one, got {order}")
    result: dict[int, int] = {}
    remainder = order
    prime = 2
    while prime * prime <= remainder:
        power = 1
        while remainder % prime == 0:
            power *= prime
            remainder //= prime
        if power > 1:
            result[prime] = power
        prime += 1
    if remainder > 1:
        result[remainder] = remainder
    return result


def normalize_group(compact: str) -> dict[str, Any]:
    free_rank = 0
    primary: dict[int, list[int]] = {}
    factors = compact.split("+")
    for factor in factors:
        match = FACTOR_RE.fullmatch(factor)
        require(match is not None, f"invalid compact group factor {factor!r}")
        base, exponent_text = match.groups()
        exponent = int(exponent_text or "1")
        if base == "infty":
            require(exponent == 1, "repeated infinite compact factors are unsupported")
            free_rank += 1
            continue
        order = int(base)
        if order == 1:
            require(len(factors) == 1 and exponent == 1,
                    "the trivial compact group code 1 must stand alone")
            continue
        for _ in range(exponent):
            for prime, prime_power in factor_order(order).items():
                primary.setdefault(prime, []).append(prime_power)
    for orders in primary.values():
        orders.sort()
    width = max((len(orders) for orders in primary.values()), default=0)
    invariant_factors = [1] * width
    for prime in sorted(primary):
        orders = primary[prime]
        padded = [1] * (width - len(orders)) + orders
        invariant_factors = [left * right for left, right in zip(
            invariant_factors, padded, strict=True)]
    return {
        "primary_decomposition": {
            str(prime): orders for prime, orders in sorted(primary.items())
        },
        "integral_decomposition": {
            "free_rank": free_rank,
            "torsion_invariant_factors": invariant_factors,
        },
        "torsion_order": str(math.prod(invariant_factors)),
    }


def read_toda_cells() -> list[dict[str, Any]]:
    with TODA_PATH.open(newline="", encoding="utf-8") as handle:
        rows = list(csv.DictReader(handle))
    require(len(rows) == 20, "Toda registry must contain stems 0 through 19")
    cells: list[dict[str, Any]] = []
    for expected_stem, row in enumerate(rows):
        stem = int(row["stem_k"])
        require(stem == expected_stem, f"expected Toda stem {expected_stem}, got {stem}")
        for n in range(1, 21):
            cells.append({
                "id": f"toda-k{stem}-n{n}",
                "n": n,
                "stem": stem,
                "m": n + stem,
                "status": "exact_integral",
                "group": normalize_group(row[f"n_{n}"]),
                "source_refs": [{
                    "source_id": "toda1962",
                    "locator": "Appendix table transcribed in the audited report, Appendix B",
                    "scope": "complete integral additive group",
                }],
            })
    return cells


def read_mimura_toda_cells() -> list[dict[str, Any]]:
    with MIMURA_TODA_PATH.open(newline="", encoding="utf-8") as handle:
        rows = list(csv.DictReader(handle))
    require([int(row["n"]) for row in rows] == list(range(2, 23)),
            "Mimura-Toda registry must contain n=2 through 22")
    cells: list[dict[str, Any]] = []
    for row in rows:
        n = int(row["n"])
        stem = int(row["stem_k"])
        require(stem == 20, f"Mimura-Toda row n={n}: stem must be 20")
        require(row["source_id"] == "MimuraToda1963",
                f"Mimura-Toda row n={n}: unexpected source id")
        cells.append({
            "id": f"mimura-toda-k20-n{n}",
            "n": n,
            "stem": stem,
            "m": n + stem,
            "status": "exact_integral",
            "group": normalize_group(row["compact_group"]),
            "source_refs": [{
                "source_id": "MimuraToda1963",
                "locator": row["source_locator"],
                "scope": "complete integral additive group",
            }],
        })
    return cells


def build_payload() -> dict[str, Any]:
    cells = read_toda_cells() + read_mimura_toda_cells()
    require(len(cells) == 421, f"expected 421 explicit low-stem cells, got {len(cells)}")
    require(len({(cell['n'], cell['stem']) for cell in cells}) == len(cells),
            "low-stem registry contains duplicate coordinates")
    return {
        "schema_version": "1.0.0",
        "registry_version": "2026-08-12.1",
        "reviewed_on": "2026-08-12",
        "title": "Exact integral low-stem lattice groups",
        "coverage": {
            "toda_stems": {"stem_min": 0, "stem_max": 19, "n_min": 1, "n_max": 20},
            "mimura_toda_stem": {"stem": 20, "n_min": 2, "n_max": 22},
            "explicit_cell_count": len(cells),
            "extension_rule": "For larger n, the lattice resolves these stems from the exact stable registry.",
        },
        "sources": [
            {
                "source_id": "toda1962",
                "title": "Composition Methods in Homotopy Groups of Spheres",
                "citation": "Hirosi Toda, Annals of Mathematics Studies 49, Princeton University Press, 1962.",
                "url": "https://doi.org/10.1515/9781400882140",
                "publication_status": "published",
            },
            {
                "source_id": "MimuraToda1963",
                "title": "The (n+20)-th homotopy groups of n-spheres",
                "citation": "Mamoru Mimura and Hirosi Toda, J. Math. Kyoto Univ. 3-1 (1963), 37-58.",
                "doi": "10.1215/kjm/1250524854",
                "url": "https://doi.org/10.1215/kjm/1250524854",
                "publication_status": "published",
            },
        ],
        "cells": cells,
    }


def render(payload: dict[str, Any]) -> str:
    return json.dumps(payload, indent=2, ensure_ascii=False) + "\n"


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args(argv)
    try:
        expected = render(build_payload())
    except (OSError, RegistryError) as error:
        print(f"low-stem lattice generation failed: {error}", file=sys.stderr)
        return 2
    if args.check:
        actual = OUTPUT_PATH.read_text(encoding="utf-8") if OUTPUT_PATH.is_file() else ""
        if actual != expected:
            print(f"stale generated lattice data: {OUTPUT_PATH.relative_to(ROOT)}", file=sys.stderr)
            return 1
        print("low-stem lattice data current (421 explicit exact groups)")
        return 0
    OUTPUT_PATH.parent.mkdir(parents=True, exist_ok=True)
    OUTPUT_PATH.write_text(expected, encoding="utf-8")
    print("generated website/public/data/low-stem-exact.json (421 exact groups)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
