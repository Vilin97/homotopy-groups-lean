#!/usr/bin/env python3
"""Generate the stable-stem Lean benchmark module and per-stem manifests.

The research registry is the sole mathematical data source. Run with --check in
CI to ensure the committed generated files exactly match it.
"""

from __future__ import annotations

import argparse
import json
import math
import pathlib
import sys
from typing import Any


REPO_ROOT = pathlib.Path(__file__).resolve().parent.parent
SOURCE_PATH = REPO_ROOT / "research" / "stable-stems.json"
LEAN_PATH = REPO_ROOT / "HomotopyGroups" / "StableStems.lean"
MANIFEST_DIR = REPO_ROOT / "manifests" / "problems"
MODULE_NAME = "HomotopyGroups.StableStems"
FIRST_STEM = 0
LAST_STEM = 90
NON_EXACT_ALTERNATIVE_COUNTS = {84: 2, 85: 4, 86: 2, 90: 2}
SUPERSEDED_STEMS = {70, 71, 82, 83}
LEAN_PROOFS = {
    0: "exact Submission.pi2_sphere_two_at_mulEquiv_int (stableSphereBasepoint 2)",
}


class RegistryError(ValueError):
    """Raised when the research registry violates the generation contract."""


def require(condition: bool, message: str) -> None:
    if not condition:
        raise RegistryError(message)


def is_prime(value: int) -> bool:
    if value < 2:
        return False
    divisor = 2
    while divisor * divisor <= value:
        if value % divisor == 0:
            return False
        divisor += 1
    return True


def is_power_of(value: int, prime: int) -> bool:
    if value < prime:
        return False
    while value % prime == 0:
        value //= prime
    return value == 1


def canonical_invariant_factors(primary: dict[str, list[int]]) -> list[int]:
    """Combine sorted primary cyclic orders into integral invariant factors."""

    width = max((len(orders) for orders in primary.values()), default=0)
    factors = [1] * width
    for orders in primary.values():
        padded = [1] * (width - len(orders)) + orders
        factors = [left * right for left, right in zip(factors, padded, strict=True)]
    return factors


def validate_group(raw: Any, label: str) -> dict[str, Any]:
    require(isinstance(raw, dict), f"{label}: group must be an object")
    primary = raw.get("primary_decomposition")
    integral = raw.get("integral_decomposition")
    torsion_order_raw = raw.get("torsion_order")
    require(isinstance(primary, dict), f"{label}: primary_decomposition must be an object")
    require(isinstance(integral, dict), f"{label}: integral_decomposition must be an object")
    require(
        isinstance(torsion_order_raw, str) and torsion_order_raw.isdecimal(),
        f"{label}: torsion_order must be a decimal string",
    )

    normalized_primary: dict[str, list[int]] = {}
    for prime_text, orders_raw in primary.items():
        require(prime_text.isdecimal(), f"{label}: invalid prime key {prime_text!r}")
        prime = int(prime_text)
        require(is_prime(prime), f"{label}: primary key {prime} is not prime")
        require(isinstance(orders_raw, list), f"{label}: orders at {prime} must be a list")
        require(
            all(isinstance(order, int) and not isinstance(order, bool) for order in orders_raw),
            f"{label}: cyclic orders at {prime} must be integers",
        )
        orders = list(orders_raw)
        require(orders == sorted(orders), f"{label}: cyclic orders at {prime} are not sorted")
        require(
            all(is_power_of(order, prime) for order in orders),
            f"{label}: a cyclic order at {prime} is not a positive power of {prime}",
        )
        normalized_primary[prime_text] = orders

    free_rank = integral.get("free_rank")
    factors_raw = integral.get("torsion_invariant_factors")
    require(
        isinstance(free_rank, int) and not isinstance(free_rank, bool) and free_rank >= 0,
        f"{label}: free_rank must be a nonnegative integer",
    )
    require(isinstance(factors_raw, list), f"{label}: invariant factors must be a list")
    require(
        all(isinstance(factor, int) and not isinstance(factor, bool) and factor > 1
            for factor in factors_raw),
        f"{label}: invariant factors must be integers greater than one",
    )
    factors = list(factors_raw)
    require(
        all(right % left == 0 for left, right in zip(factors, factors[1:])),
        f"{label}: invariant factors do not form a divisibility chain",
    )
    expected_factors = canonical_invariant_factors(normalized_primary)
    require(
        factors == expected_factors,
        f"{label}: invariant factors {factors} disagree with primary data {expected_factors}",
    )
    expected_order = math.prod(factors)
    require(
        int(torsion_order_raw) == expected_order,
        f"{label}: torsion_order {torsion_order_raw} should be {expected_order}",
    )
    return {
        "free_rank": free_rank,
        "factors": factors,
        "torsion_order": torsion_order_raw,
    }


def validate_source_refs(
    row: dict[str, Any], sources: dict[str, dict[str, Any]], label: str
) -> None:
    refs = row.get("source_refs")
    require(isinstance(refs, list) and refs, f"{label}: source_refs must be nonempty")
    for ref in refs:
        require(isinstance(ref, dict), f"{label}: each source reference must be an object")
        source_id = ref.get("source_id")
        require(source_id in sources, f"{label}: unknown source id {source_id!r}")
        require(
            isinstance(ref.get("locator"), str) and ref["locator"],
            f"{label}: source locator must be nonempty",
        )
        require(
            isinstance(ref.get("scope"), str) and ref["scope"],
            f"{label}: source scope must be nonempty",
        )


def load_and_validate_registry() -> dict[str, Any]:
    try:
        registry = json.loads(SOURCE_PATH.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as error:
        raise RegistryError(f"failed to read {SOURCE_PATH}: {error}") from error

    require(isinstance(registry, dict), "registry root must be an object")
    require(registry.get("schema_version") == "1.0.0", "unsupported schema_version")
    require(
        isinstance(registry.get("registry_version"), str) and registry["registry_version"],
        "registry_version must be nonempty",
    )
    coverage = registry.get("coverage")
    require(isinstance(coverage, dict), "coverage must be an object")
    require(coverage.get("first_stem") == FIRST_STEM, "coverage.first_stem must be 0")
    require(coverage.get("last_stem") == LAST_STEM, "coverage.last_stem must be 90")
    require(coverage.get("row_count") == LAST_STEM + 1, "coverage.row_count must be 91")
    require(
        coverage.get("non_exact_stems") == sorted(NON_EXACT_ALTERNATIVE_COUNTS),
        "coverage.non_exact_stems is inconsistent",
    )

    sources_raw = registry.get("sources")
    require(isinstance(sources_raw, list) and sources_raw, "sources must be nonempty")
    sources: dict[str, dict[str, Any]] = {}
    for source in sources_raw:
        require(isinstance(source, dict), "each source must be an object")
        source_id = source.get("source_id")
        require(isinstance(source_id, str) and source_id, "source_id must be nonempty")
        require(source_id not in sources, f"duplicate source_id {source_id}")
        require(
            isinstance(source.get("url"), str) and source["url"].startswith("https://"),
            f"source {source_id}: missing HTTPS URL",
        )
        require(
            isinstance(source.get("doi"), str) and source["doi"],
            f"source {source_id}: missing DOI",
        )
        sources[source_id] = source

    rows = registry.get("stems")
    require(isinstance(rows, list), "stems must be a list")
    require(len(rows) == LAST_STEM + 1, "stems must contain exactly 91 rows")
    require(
        [row.get("stem") for row in rows if isinstance(row, dict)]
        == list(range(FIRST_STEM, LAST_STEM + 1)),
        "stem rows must be objects ordered contiguously from 0 through 90",
    )

    for row in rows:
        stem = row["stem"]
        label = f"stem {stem}"
        validate_source_refs(row, sources, label)
        is_exact = row.get("is_exact")
        require(isinstance(is_exact, bool), f"{label}: is_exact must be Boolean")
        if is_exact:
            require(row.get("status") == "exact", f"{label}: exact status mismatch")
            require(stem not in NON_EXACT_ALTERNATIVE_COUNTS, f"{label}: unexpectedly exact")
            summary = validate_group(row.get("group"), label)
            require("alternatives" not in row, f"{label}: exact row has alternatives")
            if stem == 0:
                require(
                    summary["free_rank"] == 1 and not summary["factors"],
                    "stem 0 must be infinite cyclic",
                )
            else:
                require(summary["free_rank"] == 0, f"{label}: unexpected free part")
        else:
            require(
                row.get("status") == "published_alternatives",
                f"{label}: non-exact status must be published_alternatives",
            )
            require(stem in NON_EXACT_ALTERNATIVE_COUNTS, f"{label}: unexpected non-exact row")
            require("group" not in row, f"{label}: non-exact row must not select one group")
            uncertainty = row.get("uncertainty")
            require(isinstance(uncertainty, dict), f"{label}: uncertainty must be an object")
            require(
                uncertainty.get("alternatives_are_full_integral_groups") is True,
                f"{label}: alternatives must be complete integral groups",
            )
            alternatives = row.get("alternatives")
            require(isinstance(alternatives, list), f"{label}: alternatives must be a list")
            require(
                len(alternatives) == NON_EXACT_ALTERNATIVE_COUNTS[stem],
                f"{label}: wrong number of published alternatives",
            )
            seen_ids: set[str] = set()
            seen_groups: set[tuple[int, tuple[int, ...]]] = set()
            for alternative in alternatives:
                require(isinstance(alternative, dict), f"{label}: alternative must be an object")
                alternative_id = alternative.get("alternative_id")
                require(
                    isinstance(alternative_id, str) and alternative_id,
                    f"{label}: alternative_id must be nonempty",
                )
                require(alternative_id not in seen_ids, f"{label}: duplicate alternative id")
                seen_ids.add(alternative_id)
                summary = validate_group(alternative.get("group"), f"{label} {alternative_id}")
            require(summary["free_rank"] == 0, f"{label}: unexpected free alternative")
            signature = (summary["free_rank"], tuple(summary["factors"]))
            require(signature not in seen_groups, f"{label}: duplicate group alternative")
            seen_groups.add(signature)

    exact_stems = {row["stem"] for row in rows if row["is_exact"]}
    require(
        set(LEAN_PROOFS) <= exact_stems,
        "every configured Lean proof must target an exact registry stem",
    )

    supersession_rules = registry.get("supersession_rules")
    require(isinstance(supersession_rules, list), "supersession_rules must be a list")
    superseded = {
        stem
        for rule in supersession_rules
        if isinstance(rule, dict)
        for stem in rule.get("stems", [])
    }
    require(superseded == SUPERSEDED_STEMS, "supersession rules must cover 70, 71, 82, 83")
    for stem in SUPERSEDED_STEMS:
        row = rows[stem]
        source_ids = {ref["source_id"] for ref in row["source_refs"]}
        require(source_ids == {"iwx2023", "bix2025"}, f"stem {stem}: supersession sources missing")
        require(
            isinstance(row.get("note"), str) and row["note"],
            f"stem {stem}: supersession note missing",
        )

    registry["_sources_by_id"] = sources
    return registry


def nested_product(factors: list[int]) -> str:
    require(bool(factors), "cannot render an empty product")
    expression = f"ZMod {factors[-1]}"
    for factor in reversed(factors[:-1]):
        expression = f"ZMod {factor} × ({expression})"
    return expression


def lean_group_type(group: dict[str, Any]) -> str:
    integral = group["integral_decomposition"]
    free_rank = integral["free_rank"]
    factors = integral["torsion_invariant_factors"]
    if free_rank == 1:
        require(not factors, "the generator only supports the registry's torsion-free rank-one row")
        return "Multiplicative ℤ"
    require(free_rank == 0, "the generator only supports free ranks zero and one")
    if not factors:
        return "Multiplicative (ZMod 1)"
    return f"Multiplicative ({nested_product(factors)})"


def human_group(group: dict[str, Any]) -> str:
    integral = group["integral_decomposition"]
    free_rank = integral["free_rank"]
    factors = integral["torsion_invariant_factors"]
    summands: list[str] = []
    if free_rank:
        summands.extend(["Z"] * free_rank)
    summands.extend(f"Z/{factor}" for factor in factors)
    return "0" if not summands else " x ".join(summands)


def theorem_name(stem: int) -> str:
    return f"stable_stem_{stem:03d}"


def stable_domain(stem: int) -> str:
    sphere_dimension = stem + 2
    homotopy_degree = 2 * stem + 2
    return (
        f"π_ {homotopy_degree} (StableSphere {sphere_dimension}) "
        f"(stableSphereBasepoint {sphere_dimension})"
    )


def equivalence_proposition(stem: int, group: dict[str, Any]) -> str:
    return (
        "Nonempty\n"
        f"      ({stable_domain(stem)} ≃*\n"
        f"        {lean_group_type(group)})"
    )


def source_description(row: dict[str, Any], sources: dict[str, dict[str, Any]]) -> str:
    pieces: list[str] = []
    for ref in row["source_refs"]:
        source = sources[ref["source_id"]]
        pieces.append(
            f"{ref['source_id']} {ref['locator']}: {source['url']} "
            f"(DOI https://doi.org/{source['doi']})"
        )
    return "; ".join(pieces)


def row_notes(row: dict[str, Any], registry_version: str) -> str:
    stem = row["stem"]
    sphere_dimension = stem + 2
    homotopy_degree = 2 * stem + 2
    if stem in LEAN_PROOFS:
        status = "knowledge_status=formalized_local"
        group_text = (
            f"Integral invariant factors: {human_group(row['group'])}. "
            "The exact benchmark declaration is Lean-kernel checked."
        )
    elif row["is_exact"]:
        status = "knowledge_status=known_result/exact"
        group_text = f"Integral invariant factors: {human_group(row['group'])}."
    else:
        status = "knowledge_status=open_computation/published_alternatives"
        alternatives = ", ".join(
            f"{alternative['alternative_id']}={human_group(alternative['group'])}"
            for alternative in row["alternatives"]
        )
        group_text = (
            "The theorem states the complete alternatives published by the source; "
            f"unresolved computation remains. Alternatives: {alternatives}."
        )
    pieces = [
        status,
        (
            f"Stable representative pi_{homotopy_degree}(S^{sphere_dimension}) lies at "
            "the Freudenthal isomorphism bound q=2n-2."
        ),
        group_text,
        f"Generated from research/stable-stems.json registry {registry_version}.",
    ]
    if note := row.get("note"):
        pieces.append(note)
    return " ".join(pieces)


def render_doc_comment(row: dict[str, Any], sources: dict[str, dict[str, Any]]) -> list[str]:
    stem = row["stem"]
    sphere_dimension = stem + 2
    homotopy_degree = 2 * stem + 2
    lines = [
        "/--",
        f"Stable stem {stem}, represented by pi_{homotopy_degree}(S^{sphere_dimension}).",
        "The equality q = 2n - 2 places this representative in the Freudenthal stable range.",
    ]
    if row["is_exact"]:
        lines.append(f"Published integral group: {human_group(row['group'])}.")
    else:
        lines.append("Published complete integral-group alternatives:")
        for alternative in row["alternatives"]:
            lines.append(
                f"* {alternative['alternative_id']}: {human_group(alternative['group'])}."
            )
        lines.append("Knowledge status: open computation with published alternatives.")
    if note := row.get("note"):
        lines.append(note)
    lines.append(f"Sources: {source_description(row, sources)}")
    lines.append("-/")
    return lines


def render_theorem(row: dict[str, Any], sources: dict[str, dict[str, Any]]) -> str:
    stem = row["stem"]
    lines = render_doc_comment(row, sources)
    lines.extend(["@[eval_problem]", f"theorem {theorem_name(stem)} :"])
    if row["is_exact"]:
        proposition = equivalence_proposition(stem, row["group"])
        lines.append(f"    {proposition} := by")
    else:
        propositions = [
            equivalence_proposition(stem, alternative["group"])
            for alternative in row["alternatives"]
        ]
        for index, proposition in enumerate(propositions):
            suffix = " ∨" if index + 1 < len(propositions) else " := by"
            lines.append(f"    ({proposition}){suffix}")
    if stem in LEAN_PROOFS:
        lines.append(f"  {LEAN_PROOFS[stem]}")
    else:
        lines.append("  sorry")
    return "\n".join(lines)


def render_lean(registry: dict[str, Any]) -> str:
    sources = registry["_sources_by_id"]
    theorem_blocks = "\n\n".join(render_theorem(row, sources) for row in registry["stems"])
    return f"""/-
This file is generated by `scripts/generate_stable_stems.py` from
`research/stable-stems.json` (registry {registry['registry_version']}).
Do not edit it by hand.
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.ZMod.Basic
import Mathlib.Topology.Homotopy.HomotopyGroup
import EvalTools.Markers
import Submission.Pi2SphereTwoGeneric

open scoped Topology

namespace HomotopyGroups.StableStems

/-- The unit metric sphere modeling `S^n`. -/
abbrev StableSphere (n : ℕ) :=
  Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1

/-- The first coordinate vector gives the basepoint used for every modeled sphere. -/
noncomputable def stableSphereBasepoint (n : ℕ) : StableSphere n :=
  ⟨EuclideanSpace.single 0 1, by simp [StableSphere]⟩

{theorem_blocks}

end HomotopyGroups.StableStems
"""


def toml_string(value: str) -> str:
    """Render a TOML basic string using its JSON-compatible escape subset."""

    return json.dumps(value, ensure_ascii=False)


def render_manifest(
    row: dict[str, Any], registry: dict[str, Any]
) -> str:
    stem = row["stem"]
    name = theorem_name(stem)
    sphere_dimension = stem + 2
    homotopy_degree = 2 * stem + 2
    title = f"Stable stem {stem}: pi_{homotopy_degree}(S^{sphere_dimension})"
    source = source_description(row, registry["_sources_by_id"])
    notes = row_notes(row, registry["registry_version"])
    return "\n".join(
        [
            f"id = {toml_string(name)}",
            f"title = {toml_string(title)}",
            "test = false",
            f"module = {toml_string(MODULE_NAME)}",
            f"holes = [{toml_string(name)}]",
            f"submitter = {toml_string('homotopy-groups-lean research registry')}",
            f"source = {toml_string(source)}",
            f"notes = {toml_string(notes)}",
            "",
        ]
    )


def desired_outputs(registry: dict[str, Any]) -> dict[pathlib.Path, str]:
    outputs = {LEAN_PATH: render_lean(registry)}
    for row in registry["stems"]:
        outputs[MANIFEST_DIR / f"{theorem_name(row['stem'])}.toml"] = render_manifest(
            row, registry
        )
    return outputs


def check_outputs(outputs: dict[pathlib.Path, str]) -> list[str]:
    problems: list[str] = []
    for path, expected in outputs.items():
        try:
            actual = path.read_text(encoding="utf-8")
        except FileNotFoundError:
            problems.append(f"missing {path.relative_to(REPO_ROOT)}")
            continue
        except OSError as error:
            problems.append(f"cannot read {path.relative_to(REPO_ROOT)}: {error}")
            continue
        if actual != expected:
            problems.append(f"stale {path.relative_to(REPO_ROOT)}")
    expected_manifests = {path.resolve() for path in outputs if path.parent == MANIFEST_DIR}
    for path in sorted(MANIFEST_DIR.glob("stable_stem_*.toml")):
        if path.resolve() not in expected_manifests:
            problems.append(f"unexpected {path.relative_to(REPO_ROOT)}")
    return problems


def write_outputs(outputs: dict[pathlib.Path, str]) -> None:
    for path, content in outputs.items():
        path.parent.mkdir(parents=True, exist_ok=True)
        if path.exists() and path.read_text(encoding="utf-8") == content:
            continue
        path.write_text(content, encoding="utf-8")


def parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--check",
        action="store_true",
        help="Fail if committed generated files differ from the source registry.",
    )
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    args = parse_args(argv)
    try:
        registry = load_and_validate_registry()
        outputs = desired_outputs(registry)
    except RegistryError as error:
        print(f"stable-stem registry error: {error}", file=sys.stderr)
        return 2

    if args.check:
        problems = check_outputs(outputs)
        if problems:
            for problem in problems:
                print(problem, file=sys.stderr)
            return 1
        print(f"stable-stem generated files are current ({len(registry['stems'])} stems)")
        return 0

    unexpected = [
        path
        for path in MANIFEST_DIR.glob("stable_stem_*.toml")
        if path.resolve() not in {output.resolve() for output in outputs}
    ]
    if unexpected:
        for path in sorted(unexpected):
            print(f"refusing to overwrite unexpected {path.relative_to(REPO_ROOT)}", file=sys.stderr)
        return 1
    write_outputs(outputs)
    print(f"generated {LEAN_PATH.relative_to(REPO_ROOT)} and {len(registry['stems'])} manifests")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
