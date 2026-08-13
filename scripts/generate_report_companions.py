#!/usr/bin/env python3
"""Generate the three machine-readable companions named in Appendix F.

The stable CSV is derived from the audited JSON registry.  The Toda CSV is a
literal transcription of Appendix B's compact notation; keeping the compact
entries avoids inventing generator or extension data absent from the table.
"""

from __future__ import annotations

import argparse
import csv
import json
import shutil
import sys
import tempfile
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
OUTPUT = ROOT / "research" / "report-data"
PUBLIC_OUTPUT = ROOT / "website" / "public" / "reports"
COMPANION_NAMES = (
    "stable_stems_0_90.csv",
    "toda_unstable_stems_0_19.csv",
    "homotopy_spheres_bibliography.bib",
)

TODA_LEFT = """
0 infty infty infty infty infty infty infty infty infty infty
1 1 infty 2 2 2 2 2 2 2 2
2 1 2 2 2 2 2 2 2 2 2
3 1 2 4+3 infty+4+3 8+3 8+3 8+3 8+3 8+3 8+3
4 1 4+3 2 2^2 2 1 1 1 1 1
5 1 2 2 2^2 2 infty 1 1 1 1
6 1 2 3 8+3+3 2 2 2 2 2 2
7 1 3 3+5 3+5 2+3+5 4+3+5 8+3+5 infty+8+3+5 16+3+5 16+3+5
8 1 3+5 2 2 2 8+2+3 2^3 2^4 2^2 2^2
9 1 2 2^2 2^3 2^3 2^3 2^4 2^5 2^4 infty+2^3
10 1 2^2 4+2+3 8+4+2+3^2+5 8+2+9 8+2+9 8+3+2 8^2+2+3^2 8+2+3 4+2+3
11 1 4+2+3 4+2^2+3+7 4+2^5+3+7 8+2^2+9+7 8+4+9+7 8+2+9+7 8+2+9+7 8+2+9+7 8+2+9+7
12 1 4+2^2+3+7 2^2 2^6 2^3 16+3+5 1 1 1 4+3
13 1 2^2 2+3 8+2^2+3^2 2^2+3 2+3 2+3 2^2+3 2+3 2+3
14 1 2+3 2+3+5 8+2^2+9+3+5+7 2^2+3 4+2+3 8+4+3 16+8+4+3^2+5 16+4 16+2
15 1 2+3+5 2+3+5 2+3+5 2^2+3+5 4+2+3^2+5 8+2^3+3+5 8+2^5+3+5 16+2^3+3+5 16+2^2+3+5
16 1 2+3+5 2^2+3 2^3+3^2 2^2 8+2^2+9+7 2^4 2^7 2^4 16+2+3+5
17 1 2^2+3 4+2^2+3 8+4^2+2^2+3^2 4+2^2 2^4 2^4 2^5+3 2^4 2^3
18 1 4+2^2+3 4+2^2+3 8+4+2^5+3^2+5 8+2^2+3 8+2^2+3^2 8+2^2+3 8^2+2+9+3+7 8+2+3 8+2^2+3
19 1 4+2^2+3 4+2+3+11 4+2^5+3+11 8+2+3+11 32+8+3+11 8+2+3+11 8+2+3+11 8+2+3+11 8+2+3^2+11
"""

TODA_RIGHT = """
0 infty infty infty infty infty infty infty infty infty infty infty
1 2 2 2 2 2 2 2 2 2 2 2
2 2 2 2 2 2 2 2 2 2 2 2
3 8+3 8+3 8+3 8+3 8+3 8+3 8+3 8+3 8+3 8+3 8+3
4 1 1 1 1 1 1 1 1 1 1 1
5 1 1 1 1 1 1 1 1 1 1 1
6 2 2 2 2 2 2 2 2 2 2 2
7 16+3+5 16+3+5 16+3+5 16+3+5 16+3+5 16+3+5 16+3+5 16+3+5 16+3+5 16+3+5 16+3+5
8 2^2 2^2 2^2 2^2 2^2 2^2 2^2 2^2 2^2 2^2 2^2
9 2^3 2^3 2^3 2^3 2^3 2^3 2^3 2^3 2^3 2^3 2^3
10 2^2+3 2+3 2+3 2+3 2+3 2+3 2+3 2+3 2+3 2+3 2+3
11 8+9+7 infty+8+9+7 8+9+7 8+9+7 8+9+7 8+9+7 8+9+7 8+9+7 8+9+7 8+9+7 8+9+7
12 2 2^2 2 1 1 1 1 1 1 1 1
13 2^2+3 2^2+3 2+3 infty+3 3 3 3 3 3 3 3
14 16+2 16+4+2+3 16+2 8+2 4+2 2^2 2^2 2^2 2^2 2^2 2^2
15 16+2+3+5 16+2+3+5 32+2+3+5 32+2+3+5 32+2+3+5 infty+32+2+3+5 32+2+3+5 32+2+3+5 32+2+3+5 32+2+3+5 32+2+3+5
16 2 2 2 8+2+3 2^3 2^4 2^3 2^2 2^2 2^2 2^2
17 2^3 2^4 2^4 2^4 2^5 2^6 2^5 infty+2^4 2^4 2^4 2^4
18 8+4+2 32+4^2+2+3+5 8^2+2 8^2+2 8^2+2 8^3+2+3 8^2+2 8+4+2 8+2^2 8+2 8+2
19 8+2^3+3+11 8+2^5+3+11 8+2^3+3+11 8+4+2+3+11 8+2^2+3+11 8+2^2+3+11 8+2^2+3+11 8+2+3+11 8+2+3+11 infty+8+2+3+11 8+2+3+11
"""

BIBLIOGRAPHY = r"""@book{Toda1962,
  author = {Toda, Hirosi}, title = {Composition Methods in Homotopy Groups of Spheres},
  series = {Annals of Mathematics Studies}, volume = {49}, publisher = {Princeton University Press}, year = {1962}
}
@article{MimuraToda1963,
  author = {Mimura, Mamoru and Toda, Hirosi}, title = {The $(n+20)$-th homotopy groups of $n$-spheres},
  journal = {J. Math. Kyoto Univ.}, volume = {3}, year = {1963}, pages = {37--58}, doi = {10.1215/kjm/1250524854}
}
@article{Serre1951,
  author = {Serre, Jean-Pierre}, title = {Homologie singuli\`ere des espaces fibr\'es. Applications},
  journal = {Ann. of Math.}, volume = {54}, year = {1951}, pages = {425--505}, doi = {10.2307/1969485}
}
@article{IsaksenWangXu2023,
  author = {Isaksen, Daniel C. and Wang, Guozhen and Xu, Zhouli},
  title = {Stable homotopy groups of spheres: from dimension 0 to 90},
  journal = {Publ. Math. Inst. Hautes \'Etudes Sci.}, volume = {137}, year = {2023}, pages = {107--243}, doi = {10.1007/s10240-023-00139-1}
}
@article{BurklundIsaksenXu2025,
  author = {Burklund, Robert and Isaksen, Daniel C. and Xu, Zhouli},
  title = {Classical Stable Homotopy Groups of Spheres via F_2-Synthetic Methods},
  journal = {Peking Math. J.}, year = {2025}, doi = {10.1007/s42543-025-00098-y}
}
@article{Bousfield1985,
  author = {Bousfield, A. K.}, title = {On the homotopy theory of K-local spectra at an odd prime},
  journal = {Amer. J. Math.}, volume = {107}, number = {4}, year = {1985}, pages = {895--932}, doi = {10.2307/2374361}
}
@article{InoueMiyauchiMukai2015,
  author = {Inoue, Tomohisa and Miyauchi, Toshiyuki and Mukai, Juno},
  title = {The 2-components of the 31-stem homotopy groups of the 9 and 10-spheres},
  journal = {J. Fac. Sci. Shinshu Univ.}, volume = {46}, year = {2015}, pages = {1--19}
}
@article{MikhailovWu2013,
  author = {Mikhailov, Roman and Wu, Jie}, title = {Combinatorial group theory and the homotopy groups of finite complexes},
  journal = {Geom. Topol.}, volume = {17}, year = {2013}, pages = {235--272}, doi = {10.2140/gt.2013.17.235}
}
@article{IvanovMikhailovWu2016,
  author = {Ivanov, Sergei O. and Mikhailov, Roman and Wu, Jie}, title = {On nontriviality of certain homotopy groups of spheres},
  journal = {Homology Homotopy Appl.}, volume = {18}, number = {2}, year = {2016}, pages = {337--344}, doi = {10.4310/HHA.2016.v18.n2.a18}
}
@misc{YangWu2024,
  author = {Yang, Xiangjun and Wu, Jie}, title = {The 2-primary 33-stem homotopy groups of spheres},
  year = {2024}, eprint = {2406.08621}, archivePrefix = {arXiv}
}
@misc{BurklundHahnLevySchlank2023,
  author = {Burklund, Robert and Hahn, Jeremy and Levy, Ishan and Schlank, Tomer},
  title = {The chromatic nullstellensatz}, year = {2023}, eprint = {2310.17459}, archivePrefix = {arXiv}
}
@misc{BobkovaQuigley2024,
  author = {Bobkova, Irina and Quigley, J. D.}, title = {New simple $\eta$-torsion families of elements in the stable stems},
  year = {2024}, eprint = {2410.21181}, archivePrefix = {arXiv}, note = {Current version v3, 2026-04-03}
}
@misc{LiLi2026,
  author = {Li, Ang and Li, Jixuan}, title = {The e-family and the New Doomsday Conjecture},
  year = {2026}, eprint = {2602.20184}, archivePrefix = {arXiv}
}
"""


def _rows(block: str, expected_values: int) -> dict[int, list[str]]:
    rows: dict[int, list[str]] = {}
    for line in block.strip().splitlines():
        fields = line.split()
        stem = int(fields[0])
        values = fields[1:]
        if len(values) != expected_values:
            raise ValueError(f"Toda row {stem}: expected {expected_values}, got {len(values)}")
        rows[stem] = values
    if sorted(rows) != list(range(20)):
        raise ValueError("Toda transcription must contain stems 0 through 19")
    return rows


def _group_text(group: dict[str, object]) -> str:
    decomposition = group["integral_decomposition"]
    assert isinstance(decomposition, dict)
    rank = int(decomposition["free_rank"])
    factors = list(decomposition["torsion_invariant_factors"])
    pieces = (["Z"] * rank) + [f"Z/{factor}" for factor in factors]
    return " + ".join(pieces) or "0"


def write_stable_csv(output: Path) -> None:
    registry = json.loads((ROOT / "research" / "stable-stems.json").read_text())
    with (output / "stable_stems_0_90.csv").open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(
            handle,
            fieldnames=[
                "stem", "status", "integral_group", "published_alternatives",
                "primary_decomposition", "source_ids", "note",
            ],
            lineterminator="\n",
        )
        writer.writeheader()
        for row in registry["stems"]:
            alternatives = ""
            if not row["is_exact"]:
                alternatives = " | ".join(_group_text(item["group"]) for item in row["alternatives"])
            writer.writerow({
                "stem": row["stem"],
                "status": row["status"],
                "integral_group": _group_text(row["group"]) if row.get("group") else "",
                "published_alternatives": alternatives,
                "primary_decomposition": json.dumps(row.get("group", {}).get("primary_decomposition", {}), sort_keys=True, separators=(",", ":")),
                "source_ids": ";".join(ref["source_id"] for ref in row["source_refs"]),
                "note": row.get("note", ""),
            })


def write_toda_csv(output: Path) -> None:
    left = _rows(TODA_LEFT, 10)
    right = _rows(TODA_RIGHT, 11)
    fields = ["stem_k"] + [f"n_{n}" for n in range(1, 21)] + ["stable"]
    with (output / "toda_unstable_stems_0_19.csv").open("w", newline="", encoding="utf-8") as handle:
        writer = csv.writer(handle, lineterminator="\n")
        writer.writerow(fields)
        for stem in range(20):
            writer.writerow([stem, *left[stem], *right[stem]])


def write_outputs(output: Path) -> None:
    output.mkdir(parents=True, exist_ok=True)
    write_stable_csv(output)
    write_toda_csv(output)
    (output / "homotopy_spheres_bibliography.bib").write_text(
        BIBLIOGRAPHY, encoding="utf-8"
    )


def copy_outputs(source: Path, destination: Path) -> None:
    destination.mkdir(parents=True, exist_ok=True)
    for name in COMPANION_NAMES:
        shutil.copyfile(source / name, destination / name)


def check_outputs() -> bool:
    """Return whether repository and public copies are byte-for-byte current."""
    with tempfile.TemporaryDirectory(prefix="homotopy-report-data-") as tmp:
        generated = Path(tmp)
        write_outputs(generated)
        stale = [
            str(committed.relative_to(ROOT))
            for destination in (OUTPUT, PUBLIC_OUTPUT)
            for name in COMPANION_NAMES
            for committed in (destination / name,)
            if not committed.is_file()
            or committed.read_bytes() != (generated / name).read_bytes()
        ]
    if stale:
        print(
            "Stale report companion file(s): " + ", ".join(stale),
            file=sys.stderr,
        )
        return False
    return True


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--check",
        action="store_true",
        help="fail if the committed companion files differ from generated output",
    )
    args = parser.parse_args()
    if args.check:
        raise SystemExit(0 if check_outputs() else 1)
    write_outputs(OUTPUT)
    copy_outputs(OUTPUT, PUBLIC_OUTPUT)


if __name__ == "__main__":
    main()
