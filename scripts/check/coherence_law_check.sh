#!/usr/bin/env bash
# LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
# Copyright (C) 2026 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only
# Policy:
# - The main coherence risk in the law layer is relation-split duplication:
#   restating the same law separately for incompatible notions such as `≈`,
#   `⊑`, or strict equality.
# - The preferred architecture is to state a law once when possible and index it
#   by `LogOS.LT.Coherence.CohMode` / `CohRel`, exposing refinement-facing
#   modes publicly and leaving strict witnesses quarantined.
# - This check is heuristic. It rewards visible mode-indexed law declarations
#   and tracks unindexed relation-split law families in default lanes.

set -euo pipefail

CHECK_NAME="coherence-law-check"
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
# shellcheck source=scripts/lib/check_common.sh
source "${SCRIPT_DIR}/lib/check_common.sh"

die() { check_die "${CHECK_NAME}" "$*"; }

ROOT="$(check_repo_root "${BASH_SOURCE[0]}")"
cd "${ROOT}"

check_require_cmd "${CHECK_NAME}" python3

python3 - <<'PY'
from __future__ import annotations

import json
import re
import sys
from dataclasses import dataclass
from pathlib import Path

ROOT = Path(".").resolve()
LOGOS_DIR = ROOT / "LogOS"
THRESHOLDS = ROOT / "scripts" / "coherence_law_thresholds.tsv"
OUT = ROOT / "_build" / "metrics" / "coherence_law.json"

KEYWORDS = {
    "abstract",
    "constructor",
    "data",
    "field",
    "import",
    "infix",
    "infixl",
    "infixr",
    "instance",
    "macro",
    "module",
    "mutual",
    "open",
    "pattern",
    "postulate",
    "primitive",
    "private",
    "record",
    "syntax",
    "unquoteDecl",
    "variable",
    "where",
}

LAW_FRAGMENTS = (
    "Law",
    "Laws",
    "law",
    "laws",
    "Coherence",
    "Preserves",
    "Stable",
    "Monotone",
    "Soundness",
    "Correctness",
    "Naturality",
    "Compatibility",
    "-mono",
    "-law",
    "-laws",
    "-stable",
    "-sound",
    "-correct",
)

QUARANTINE_STEMS = {
    "Checks",
    "Definitional",
    "Prelude",
    "Strictification",
}

POSITIVE_EXCLUDED_MODULES = {
    "LogOS/LT/Coherence.agda",
}

TOP_CLUSTER_LIMIT = 12


@dataclass(frozen=True)
class Thresholds:
    coherence_indexed_law_modules: int
    coherence_indexed_law_declarations: int
    unindexed_relation_split_clusters: int
    unindexed_relation_split_declarations: int


@dataclass(frozen=True)
class Declaration:
    name: str
    text: str
    law_like: bool
    coherence_indexed: bool
    relation_tag: str


def rel(path: Path) -> str:
    return path.relative_to(ROOT).as_posix()


def strip_agda_comments(text: str) -> str:
    out: list[str] = []
    i = 0
    depth = 0
    n = len(text)

    while i < n:
        if depth == 0 and text.startswith("--", i):
            while i < n and text[i] != "\n":
                i += 1
            continue

        if text.startswith("{-", i):
            depth += 1
            i += 2
            continue

        if depth > 0:
            if text.startswith("{-", i):
                depth += 1
                i += 2
                continue
            if text.startswith("-}", i):
                depth -= 1
                i += 2
                continue
            if text[i] == "\n":
                out.append("\n")
            i += 1
            continue

        out.append(text[i])
        i += 1

    return "".join(out)


def is_quarantine_path(path: Path) -> bool:
    for part in path.parts:
        stem = Path(part).stem
        if stem in QUARANTINE_STEMS:
            return True
        if stem.startswith("Strict"):
            return True
    return False


def counts_toward_positive_metric(path: Path) -> bool:
    return rel(path) not in POSITIVE_EXCLUDED_MODULES


def is_law_like(path: Path, name: str) -> bool:
    stem = path.stem
    if stem in {"Laws", "Coherence", "Definitional", "Strictification"}:
        return True
    return any(fragment in name for fragment in LAW_FRAGMENTS)


def coherence_indexed(text: str) -> bool:
    return "CohMode" in text or "CohRel" in text


def relation_tag(path: Path, name: str, text: str) -> str:
    if is_quarantine_path(path):
        return "strict"

    if name.endswith("≈") or "CohRel approx" in text or "_≈_" in text:
        return "approx"
    if name.endswith("⊑") or "CohRel under" in text or "_⊑_" in text:
        return "under"
    if name.endswith("≡") or "≡" in text or "rewrite" in text:
        return "strict"

    if re.search(r"(?:Approx|Approximate)$", name):
        return "approx"
    if re.search(r"(?:Under|Monotone)$", name):
        return "under"
    if re.search(r"(?:Strict|Definitional)$", name):
        return "strict"

    return "plain"


def normalize_stem(name: str) -> str:
    stem = name
    while stem.endswith(("≈", "⊑", "≡")):
        stem = stem[:-1]

    changed = True
    while changed:
        changed = False
        next_stem = re.sub(r"(Approx|Approximate|Under|Strict|Definitional)$", "", stem)
        next_stem = re.sub(r"(-approx|-under|-strict|-definitional)$", "", next_stem, flags=re.IGNORECASE)
        if next_stem != stem:
            stem = next_stem
            changed = True

    return stem


def extract_declarations(path: Path) -> list[Declaration]:
    text = strip_agda_comments(path.read_text(encoding="utf-8"))
    blocks: dict[str, list[str]] = {}
    current_name: str | None = None
    current_lines: list[str] = []

    def flush() -> None:
        nonlocal current_name, current_lines
        if current_name is not None:
            blocks.setdefault(current_name, []).append("\n".join(current_lines))
        current_name = None
        current_lines = []

    for line in text.splitlines():
        if not line.strip():
            if current_name is not None:
                current_lines.append(line)
            continue
        if line.startswith("{-#"):
            continue

        top_level = not line[0].isspace()
        if top_level:
            rec_match = re.match(r"^(?:record|data)\s+([A-Za-z0-9_.'₀₁₂₃₄₅₆₇₈₉⁰¹²³⁴⁵⁶⁷⁸⁹+-]+)", line)
            if rec_match:
                flush()
                current_name = rec_match.group(1)
                current_lines = [line]
                continue

            head = re.split(r"\s|:", line, maxsplit=1)[0]
            if head and head not in KEYWORDS:
                flush()
                current_name = head
                current_lines = [line]
                continue

        if current_name is not None:
            current_lines.append(line)

    flush()

    declarations: list[Declaration] = []
    for name, chunks in sorted(blocks.items()):
        merged = "\n".join(chunks)
        law_like = is_law_like(path, name)
        declarations.append(
            Declaration(
                name=name,
                text=merged,
                law_like=law_like,
                coherence_indexed=law_like and coherence_indexed(merged),
                relation_tag=relation_tag(path, name, merged),
            )
        )
    return declarations


def load_thresholds(path: Path) -> Thresholds:
    if not path.is_file():
        raise RuntimeError(f"missing thresholds file: {rel(path)}")

    raw: dict[str, str] = {}
    for i, line in enumerate(path.read_text(encoding="utf-8").splitlines(), start=1):
        stripped = line.strip()
        if not stripped or stripped.startswith("#"):
            continue
        cols = stripped.split("\t")
        if len(cols) != 2:
            raise RuntimeError(f"{rel(path)}:{i}: expected <metric><TAB><value>")
        raw[cols[0]] = cols[1]

    expected = {
        "coherence_indexed_law_modules",
        "coherence_indexed_law_declarations",
        "unindexed_relation_split_clusters",
        "unindexed_relation_split_declarations",
    }
    missing = expected - raw.keys()
    extra = raw.keys() - expected
    if missing:
        raise RuntimeError(f"{rel(path)}: missing thresholds: {', '.join(sorted(missing))}")
    if extra:
        raise RuntimeError(f"{rel(path)}: unknown thresholds: {', '.join(sorted(extra))}")

    try:
        return Thresholds(
            coherence_indexed_law_modules=int(raw["coherence_indexed_law_modules"]),
            coherence_indexed_law_declarations=int(raw["coherence_indexed_law_declarations"]),
            unindexed_relation_split_clusters=int(raw["unindexed_relation_split_clusters"]),
            unindexed_relation_split_declarations=int(raw["unindexed_relation_split_declarations"]),
        )
    except ValueError as exc:
        raise RuntimeError(f"{rel(path)}: invalid numeric threshold") from exc


def main() -> int:
    try:
        thresholds = load_thresholds(THRESHOLDS)
    except RuntimeError as exc:
        print("coherence-law-check: FAIL", file=sys.stderr)
        print(f"  - {exc}", file=sys.stderr)
        return 1

    if not LOGOS_DIR.is_dir():
        print("coherence-law-check: FAIL", file=sys.stderr)
        print("  - missing LogOS directory", file=sys.stderr)
        return 1

    files = sorted(path for path in LOGOS_DIR.rglob("*.agda") if "_build" not in path.parts)
    module_stats = {path: extract_declarations(path) for path in files}

    coherence_modules: list[Path] = []
    coherence_declarations: list[tuple[Path, Declaration]] = []
    law_declarations: list[tuple[Path, Declaration]] = []

    for path, declarations in module_stats.items():
        if is_quarantine_path(path):
            continue
        module_law_decls = [decl for decl in declarations if decl.law_like]
        law_declarations.extend((path, decl) for decl in module_law_decls)
        if not counts_toward_positive_metric(path):
            continue
        module_coherence_decls = [decl for decl in module_law_decls if decl.coherence_indexed]
        if module_coherence_decls:
            coherence_modules.append(path)
            coherence_declarations.extend((path, decl) for decl in module_coherence_decls)

    split_clusters: list[dict[str, object]] = []
    by_stem: dict[str, list[tuple[Path, Declaration]]] = {}
    for path, decl in law_declarations:
        if decl.relation_tag == "plain":
            continue
        stem = normalize_stem(decl.name)
        if not stem:
            continue
        by_stem.setdefault(stem, []).append((path, decl))

    for stem, entries in sorted(by_stem.items()):
        tags = sorted({decl.relation_tag for _, decl in entries})
        if len(tags) < 2:
            continue
        indexed = any(decl.coherence_indexed for _, decl in entries)
        split_clusters.append(
            {
                "stem": stem,
                "tags": tags,
                "indexed": indexed,
                "declarations": [
                    {
                        "module": rel(path),
                        "name": decl.name,
                        "tag": decl.relation_tag,
                    }
                    for path, decl in sorted(entries, key=lambda item: (rel(item[0]), item[1].name))
                ],
            }
        )

    unindexed_clusters = [cluster for cluster in split_clusters if not cluster["indexed"]]
    unindexed_split_declarations = sum(len(cluster["declarations"]) for cluster in unindexed_clusters)

    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(
        json.dumps(
            {
                "heuristic": {
                    "note": (
                        "Heuristic coherence-law metric: rewards visible CohMode/CohRel-indexed "
                        "law declarations in default lanes and tracks unindexed relation-split "
                        "law families as a duplication risk."
                    ),
                    "law_fragments": list(LAW_FRAGMENTS),
                    "positive_excluded_modules": sorted(POSITIVE_EXCLUDED_MODULES),
                    "quarantine_stems": sorted(QUARANTINE_STEMS),
                },
                "coherence_indexed": {
                    "modules": len(coherence_modules),
                    "declarations": len(coherence_declarations),
                    "sample_modules": [
                        {
                            "module": rel(path),
                            "declarations": [decl.name for decl in module_stats[path] if decl.coherence_indexed],
                        }
                        for path in coherence_modules[:50]
                    ],
                },
                "relation_split": {
                    "clusters": len(split_clusters),
                    "unindexed_clusters": len(unindexed_clusters),
                    "unindexed_declarations": unindexed_split_declarations,
                    "sample_unindexed_clusters": unindexed_clusters[:TOP_CLUSTER_LIMIT],
                },
                "thresholds": {
                    "coherence_indexed_law_modules_floor": thresholds.coherence_indexed_law_modules,
                    "coherence_indexed_law_declarations_floor": thresholds.coherence_indexed_law_declarations,
                    "unindexed_relation_split_clusters_ceiling": thresholds.unindexed_relation_split_clusters,
                    "unindexed_relation_split_declarations_ceiling": thresholds.unindexed_relation_split_declarations,
                },
            },
            indent=2,
            sort_keys=True,
        )
        + "\n",
        encoding="utf-8",
    )

    violations: list[str] = []
    if len(coherence_modules) < thresholds.coherence_indexed_law_modules:
        violations.append(
            "coherence-indexed law modules below floor: "
            f"{len(coherence_modules)} < {thresholds.coherence_indexed_law_modules}"
        )
    if len(coherence_declarations) < thresholds.coherence_indexed_law_declarations:
        violations.append(
            "coherence-indexed law declarations below floor: "
            f"{len(coherence_declarations)} < {thresholds.coherence_indexed_law_declarations}"
        )
    if len(unindexed_clusters) > thresholds.unindexed_relation_split_clusters:
        violations.append(
            "unindexed relation-split law clusters above ceiling: "
            f"{len(unindexed_clusters)} > {thresholds.unindexed_relation_split_clusters}"
        )
    if unindexed_split_declarations > thresholds.unindexed_relation_split_declarations:
        violations.append(
            "unindexed relation-split law declarations above ceiling: "
            f"{unindexed_split_declarations} > {thresholds.unindexed_relation_split_declarations}"
        )

    if violations:
        print("coherence-law-check: FAIL", file=sys.stderr)
        for item in violations:
            print(f"  - {item}", file=sys.stderr)
        if unindexed_clusters:
            print("  sample unindexed split clusters:", file=sys.stderr)
            for cluster in unindexed_clusters[:5]:
                desc = ", ".join(
                    f"{decl['name']}@{decl['module']}[{decl['tag']}]"
                    for decl in cluster["declarations"][:6]
                )
                print(f"    - {cluster['stem']}: {desc}", file=sys.stderr)
        print(f"  report: {rel(OUT)}", file=sys.stderr)
        return 1

    print("coherence-law-check: OK")
    print(f"  coherence-indexed law modules: {len(coherence_modules)}")
    print(f"  coherence-indexed law declarations: {len(coherence_declarations)}")
    print(f"  relation-split law clusters: {len(split_clusters)}")
    print(f"  unindexed relation-split law clusters: {len(unindexed_clusters)}")
    print(f"  unindexed relation-split law declarations: {unindexed_split_declarations}")
    if unindexed_clusters:
        print("  top unindexed split clusters:")
        for cluster in unindexed_clusters[:5]:
            desc = ", ".join(
                f"{decl['name']}@{decl['module']}[{decl['tag']}]"
                for decl in cluster["declarations"][:6]
            )
            print(f"    - {cluster['stem']}: {desc}")
    print(f"  floors: {thresholds.coherence_indexed_law_modules} modules, {thresholds.coherence_indexed_law_declarations} declarations")
    print(
        "  ceilings: "
        f"{thresholds.unindexed_relation_split_clusters} clusters, "
        f"{thresholds.unindexed_relation_split_declarations} declarations"
    )
    print(f"  report: {rel(OUT)}")
    return 0


raise SystemExit(main())
PY
