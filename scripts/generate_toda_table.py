#!/usr/bin/env python3
"""Generate the integral Toda and Mimura--Toda Lean statements and manifests.

The compact CSV files are the sole group-value sources.  Run with ``--check``
in CI to ensure that the committed Lean declarations and manifests remain
synchronized with the audited transcriptions.
"""

from __future__ import annotations

import argparse
import csv
import json
import pathlib
import re
import sys


ROOT = pathlib.Path(__file__).resolve().parents[1]
SOURCE = ROOT / "research" / "report-data" / "toda_unstable_stems_0_19.csv"
MIMURA_TODA_SOURCE = (
    ROOT / "research" / "report-data" / "mimura_toda_unstable_stem_20.csv"
)
LEAN_PATH = ROOT / "HomotopyGroups" / "TodaTable.lean"
MIMURA_TODA_LEAN_PATH = ROOT / "HomotopyGroups" / "MimuraTodaTable.lean"
MANIFEST_PATH = ROOT / "manifests" / "problems" / "toda_unstable_integral_table.toml"
MIMURA_TODA_MANIFEST_PATH = (
    ROOT / "manifests" / "problems" / "mimura_toda_unstable_integral_stem_twenty.toml"
)
MODULE_NAME = "HomotopyGroups.TodaTable"
MIMURA_TODA_MODULE_NAME = "HomotopyGroups.MimuraTodaTable"
THEOREM_NAME = "toda_unstable_integral_table"
MIMURA_TODA_THEOREM_NAME = "mimura_toda_unstable_integral_stem_twenty"
EXPECTED_FIELDS = (
    "stem_k",
    *(f"n_{n}" for n in range(1, 21)),
    "stable",
)
MIMURA_TODA_EXPECTED_FIELDS = (
    "n",
    "stem_k",
    "compact_group",
    "source_id",
    "source_locator",
)
FACTOR_RE = re.compile(r"(infty|[1-9][0-9]*)(?:\^([1-9][0-9]*))?\Z")


class TableError(ValueError):
    """Raised when the compact Toda table violates the generation contract."""


def parse_entry(text: str, label: str) -> list[tuple[str, int]]:
    """Parse one compact additive-group entry into cyclic summands."""
    factors = text.split("+")
    summands: list[tuple[str, int]] = []
    for factor in factors:
        match = FACTOR_RE.fullmatch(factor)
        if match is None:
            raise TableError(f"{label}: invalid compact factor {factor!r}")
        base, exponent_text = match.groups()
        exponent = int(exponent_text or "1")
        if base == "infty":
            if exponent != 1:
                raise TableError(f"{label}: repeated infinite cyclic factor is unsupported")
            summands.append(("infinite", 0))
            continue
        order = int(base)
        if order == 1:
            if len(factors) != 1 or exponent != 1:
                raise TableError(f"{label}: the trivial-group code 1 must stand alone")
            summands.append(("finite", 1))
            continue
        summands.extend(("finite", order) for _ in range(exponent))
    return summands


def load_table() -> list[list[list[tuple[str, int]]]]:
    try:
        with SOURCE.open(newline="", encoding="utf-8") as handle:
            reader = csv.DictReader(handle)
            if tuple(reader.fieldnames or ()) != EXPECTED_FIELDS:
                raise TableError(
                    f"expected columns {EXPECTED_FIELDS}, got {tuple(reader.fieldnames or ())}"
                )
            raw_rows = list(reader)
    except OSError as error:
        raise TableError(f"cannot read {SOURCE.relative_to(ROOT)}: {error}") from error
    if len(raw_rows) != 20:
        raise TableError(f"expected 20 stem rows, got {len(raw_rows)}")

    table: list[list[list[tuple[str, int]]]] = []
    for expected_stem, row in enumerate(raw_rows):
        try:
            stem = int(row["stem_k"])
        except (TypeError, ValueError) as error:
            raise TableError(f"row {expected_stem}: invalid stem_k") from error
        if stem != expected_stem:
            raise TableError(f"expected stem {expected_stem}, got {stem}")
        table.append([
            parse_entry(row[f"n_{n}"], f"stem {stem}, n={n}")
            for n in range(1, 21)
        ])
        # The stable column is not part of this theorem's 20-by-20 domain, but
        # validating it catches corruption of the committed Appendix B CSV.
        parse_entry(row["stable"], f"stem {stem}, stable")
    return table


def load_mimura_toda_stem_twenty() -> list[list[tuple[str, int]]]:
    """Load the complete Mimura--Toda 20-stem for sphere dimensions 2 through 22."""
    try:
        with MIMURA_TODA_SOURCE.open(newline="", encoding="utf-8") as handle:
            reader = csv.DictReader(handle)
            if tuple(reader.fieldnames or ()) != MIMURA_TODA_EXPECTED_FIELDS:
                raise TableError(
                    "expected Mimura--Toda columns "
                    f"{MIMURA_TODA_EXPECTED_FIELDS}, got {tuple(reader.fieldnames or ())}"
                )
            rows = list(reader)
    except OSError as error:
        raise TableError(
            f"cannot read {MIMURA_TODA_SOURCE.relative_to(ROOT)}: {error}"
        ) from error
    if len(rows) != 21:
        raise TableError(f"expected 21 Mimura--Toda rows, got {len(rows)}")

    table: list[list[tuple[str, int]]] = []
    for expected_n, row in zip(range(2, 23), rows, strict=True):
        try:
            n = int(row["n"])
            stem = int(row["stem_k"])
        except (TypeError, ValueError) as error:
            raise TableError(f"Mimura--Toda row n={expected_n}: invalid coordinate") from error
        if n != expected_n:
            raise TableError(f"expected Mimura--Toda n={expected_n}, got {n}")
        if stem != 20:
            raise TableError(f"Mimura--Toda row n={n}: expected stem 20, got {stem}")
        if row["source_id"] != "MimuraToda1963":
            raise TableError(f"Mimura--Toda row n={n}: unexpected source id")
        if row["source_locator"] not in {
            "Theorem, journal p. 37",
            "Theorem, journal p. 38",
        }:
            raise TableError(f"Mimura--Toda row n={n}: unexpected source locator")
        table.append(parse_entry(row["compact_group"], f"stem 20, n={n}"))
    return table


def render_code(summands: list[tuple[str, int]]) -> str:
    rendered = [
        "(.infiniteCyclic)" if kind == "infinite" else f"(.finiteCyclic {order})"
        for kind, order in summands
    ]
    result = rendered[-1]
    for left in reversed(rendered[:-1]):
        result = f".product {left} ({result})"
    return result


def render_lean(table: list[list[list[tuple[str, int]]]]) -> str:
    cases = "\n".join(
        f"  | {stem}, {n - 1} => {render_code(table[stem][n - 1])}"
        for stem in range(20)
        for n in range(1, 21)
    )
    return f'''/-
This file is generated by `scripts/generate_toda_table.py` from
`research/report-data/toda_unstable_stems_0_19.csv`.
Do not edit it by hand.
-/

import EvalTools.Markers
import HomotopyGroups.Spaces
import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.Data.ZMod.Basic

open scoped Topology

namespace HomotopyGroups

/-- A concrete syntax for the finitely generated abelian groups in Toda's table. -/
inductive TodaIntegralGroupCode where
  | infiniteCyclic
  | finiteCyclic (order : ℕ)
  | product (left right : TodaIntegralGroupCode)

namespace TodaIntegralGroupCode

/-- Interpret a table code as an actual bundled multiplicative group. -/
noncomputable def asGrp : TodaIntegralGroupCode → GrpCat
  | .infiniteCyclic => GrpCat.of (Multiplicative ℤ)
  | .finiteCyclic order => GrpCat.of (Multiplicative (ZMod order))
  | .product left right => GrpCat.of (left.asGrp × right.asGrp)

end TodaIntegralGroupCode

/--
The additive group in Appendix B at zero-based sphere index `nIndex` and stem
`k`. Thus `nIndex = 0` denotes `S^1`; both indices range from 0 through 19.
-/
def todaIntegralGroupCode (nIndex k : Fin 20) : TodaIntegralGroupCode :=
  match k.val, nIndex.val with
{cases}
  | _, _ => .finiteCyclic 1

/-- The actual group represented by `todaIntegralGroupCode`. -/
noncomputable def todaIntegralGroup (nIndex k : Fin 20) : GrpCat :=
  (todaIntegralGroupCode nIndex k).asGrp

/--
Toda's complete integral unstable table through the 19-stem, for sphere
dimensions 1 through 20. The two finite indices encode `n = nIndex + 1` and
the offset `k`; the target is therefore `pi_(n+k)(S^n)`.
-/
@[eval_problem]
theorem {THEOREM_NAME} (nIndex k : Fin 20) :
    Nonempty
      (HomotopyGroup.Pi (nIndex.val + 1 + k.val)
          (SphereSpace (nIndex.val + 1)) (sphereBasepoint (nIndex.val + 1)) ≃*
        todaIntegralGroup nIndex k) := by
  sorry

end HomotopyGroups
'''


def render_mimura_toda_lean(table: list[list[tuple[str, int]]]) -> str:
    cases = "\n".join(
        f"  | {n - 2} => {render_code(table[n - 2])}"
        for n in range(2, 23)
    )
    return f'''/-
This file is generated by `scripts/generate_toda_table.py` from
`research/report-data/mimura_toda_unstable_stem_20.csv`.
Do not edit it by hand.
-/

import HomotopyGroups.TodaTable

open scoped Topology

namespace HomotopyGroups

/-- The complete Mimura--Toda 20-stem code; `nIndex = 0` denotes `S^2`. -/
def mimuraTodaStemTwentyGroupCode (nIndex : Fin 21) : TodaIntegralGroupCode :=
  match nIndex.val with
{cases}
  | _ => .finiteCyclic 1

/-- The actual group represented by `mimuraTodaStemTwentyGroupCode`. -/
noncomputable def mimuraTodaStemTwentyGroup (nIndex : Fin 21) : GrpCat :=
  (mimuraTodaStemTwentyGroupCode nIndex).asGrp

/--
Mimura and Toda's complete integral 20-stem for sphere dimensions 2 through 22.
The finite index encodes `n = nIndex + 2`; the target is `pi_(n+20)(S^n)`.
-/
@[eval_problem]
theorem {MIMURA_TODA_THEOREM_NAME} (nIndex : Fin 21) :
    Nonempty
      (HomotopyGroup.Pi (nIndex.val + 22)
          (SphereSpace (nIndex.val + 2)) (sphereBasepoint (nIndex.val + 2)) ≃*
        mimuraTodaStemTwentyGroup nIndex) := by
  sorry

end HomotopyGroups
'''


def render_manifest() -> str:
    def quoted(value: str) -> str:
        return json.dumps(value, ensure_ascii=False)

    return "\n".join([
        f"id = {quoted(THEOREM_NAME)}",
        f"title = {quoted('Toda integral unstable table through the 19-stem')}",
        "test = false",
        f"module = {quoted(MODULE_NAME)}",
        f"holes = [{quoted(THEOREM_NAME)}]",
        f"submitter = {quoted('homotopy-groups-lean literature registry')}",
        f"source = {quoted('https://doi.org/10.1515/9781400882140')}",
        f"notes = {quoted('knowledge_status=known_result/exact; one finite-indexed theorem family states all 400 integral values pi_(n+k)(S^n) for 1<=n<=20 and 0<=k<=19; generated from the audited compact CSV transcription.')}",
        "",
    ])


def render_mimura_toda_manifest() -> str:
    def quoted(value: str) -> str:
        return json.dumps(value, ensure_ascii=False)

    return "\n".join([
        f"id = {quoted(MIMURA_TODA_THEOREM_NAME)}",
        f"title = {quoted('Mimura--Toda integral unstable 20-stem')}",
        "test = false",
        f"module = {quoted(MIMURA_TODA_MODULE_NAME)}",
        f"holes = [{quoted(MIMURA_TODA_THEOREM_NAME)}]",
        f"submitter = {quoted('homotopy-groups-lean literature registry')}",
        f"source = {quoted('https://doi.org/10.1215/kjm/1250524854')}",
        f"notes = {quoted('knowledge_status=known_result/exact; one finite-indexed theorem family states all 21 integral values pi_(n+20)(S^n) for 2<=n<=22; generated from the source-audited Mimura--Toda CSV transcription.')}",
        "",
    ])


def desired_outputs() -> dict[pathlib.Path, str]:
    table = load_table()
    mimura_toda_table = load_mimura_toda_stem_twenty()
    return {
        LEAN_PATH: render_lean(table),
        MANIFEST_PATH: render_manifest(),
        MIMURA_TODA_LEAN_PATH: render_mimura_toda_lean(mimura_toda_table),
        MIMURA_TODA_MANIFEST_PATH: render_mimura_toda_manifest(),
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--check",
        action="store_true",
        help="fail if the generated Lean module or manifest is stale",
    )
    args = parser.parse_args()
    try:
        outputs = desired_outputs()
    except TableError as error:
        print(f"Toda-table registry error: {error}", file=sys.stderr)
        return 2

    if args.check:
        stale = [
            str(path.relative_to(ROOT))
            for path, expected in outputs.items()
            if not path.is_file() or path.read_text(encoding="utf-8") != expected
        ]
        if stale:
            print("Stale Toda-table output(s): " + ", ".join(stale), file=sys.stderr)
            return 1
        print("Toda-table generated files are current (421 integral groups)")
        return 0

    for path, content in outputs.items():
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(content, encoding="utf-8")
    print("generated Toda and Mimura--Toda Lean tables and manifests")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
