#!/usr/bin/env bash
# LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
# Copyright (C) 2026 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only
# Policy:
# - The repository tracks an explicit law surface as a CI trend metric.
# - This check is heuristic: it scans top-level Agda declarations for
#   law-shaped names (`Law`, `Laws`, `Coherence`, `-law`, `-mono`, ...).
# - It guards against accidental regressions in bundled/proved structure, but it
#   is not a semantic adequacy theorem.

set -euo pipefail

CHECK_NAME="law-surface-check"
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
THRESHOLDS = ROOT / "scripts" / "law_surface_thresholds.tsv"
OUT = ROOT / "_build" / "metrics" / "law_surface.json"

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

OPPORTUNITY_EXCLUDE_PARTS = {
    "Adapters",
    "Checks",
    "Definitional",
    "Host",
    "Prelude",
    "Strictification",
}

OPPORTUNITY_EXCLUDE_NAME_FRAGMENTS = (
    "/All.agda",
    "/Axioms.agda",
    "/Definitional.agda",
    "/Demo.agda",
    "/Metamath/",
    "/Parse/",
    "/Strictification.agda",
    "/Support/",
    "/Syntax.agda",
    "/Tests.agda",
)

LAW_FRAGMENTS = (
    "Law",
    "Laws",
    "law",
    "laws",
    "Coherence",
    "EqLaw",
    "EqLaws",
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

REFINEMENT_MARKERS = (
    "⊑",
    "≈",
    "CohRel",
    "approx",
    "under",
    "Monotone",
    "Preserves",
    "Stable",
    "Soundness",
    "Correctness",
    "Naturality",
    "Compatibility",
    "preserves",
    "sound",
    "compatible",
)

STRICT_MARKERS = (
    "≡",
    "rewrite",
)

DEDICATED_LAW_STEMS = {
    "Laws",
    "Coherence",
    "Definitional",
    "Strictification",
}

QUARANTINE_STEMS = {
    "Prelude",
    "Checks",
    "Definitional",
    "Strictification",
}


@dataclass(frozen=True)
class Thresholds:
    refinement_law_modules: int
    refinement_law_module_pct: float
    refinement_law_declarations: int
    strict_default_lane_modules: int
    strict_default_lane_declarations: int


@dataclass(frozen=True)
class Declaration:
    name: str
    text: str
    structural: bool
    law_like: bool
    refinement: bool
    strict: bool


@dataclass(frozen=True)
class Opportunity:
    path: Path
    score: int
    structural: list[str]
    declarations: list[str]
    reasons: list[str]


def rel(path: Path) -> str:
    return path.relative_to(ROOT).as_posix()


def count_loc(paths: list[Path]) -> int:
    total = 0
    for path in paths:
        with path.open(encoding="utf-8") as handle:
            total += sum(1 for _ in handle)
    return total


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
        "refinement_law_modules",
        "refinement_law_module_pct",
        "refinement_law_declarations",
        "strict_default_lane_modules",
        "strict_default_lane_declarations",
    }
    missing = expected - raw.keys()
    extra = raw.keys() - expected
    if missing:
        raise RuntimeError(f"{rel(path)}: missing thresholds: {', '.join(sorted(missing))}")
    if extra:
        raise RuntimeError(f"{rel(path)}: unknown thresholds: {', '.join(sorted(extra))}")

    try:
        return Thresholds(
            refinement_law_modules=int(raw["refinement_law_modules"]),
            refinement_law_module_pct=float(raw["refinement_law_module_pct"]),
            refinement_law_declarations=int(raw["refinement_law_declarations"]),
            strict_default_lane_modules=int(raw["strict_default_lane_modules"]),
            strict_default_lane_declarations=int(raw["strict_default_lane_declarations"]),
        )
    except ValueError as exc:
        raise RuntimeError(f"{rel(path)}: invalid numeric threshold") from exc


def is_law_like(name: str) -> bool:
    return any(fragment in name for fragment in LAW_FRAGMENTS)


def module_stem(path: Path) -> str:
    return path.stem


def is_quarantine_path(path: Path) -> bool:
    for part in path.parts:
        stem = Path(part).stem
        if stem in QUARANTINE_STEMS:
            return True
        if stem.startswith("Strict"):
            return True
    return False


def is_dedicated_law_surface(path: Path) -> bool:
    stem = module_stem(path)
    return stem in DEDICATED_LAW_STEMS


def contains_any(text: str, markers: tuple[str, ...]) -> bool:
    return any(marker in text for marker in markers)


def extract_module_stats(path: Path) -> list[Declaration]:
    text = strip_agda_comments(path.read_text(encoding="utf-8"))
    blocks: dict[str, list[str]] = {}
    structural: set[str] = set()

    current_name: str | None = None
    current_lines: list[str] = []
    current_structural = False

    def flush() -> None:
        nonlocal current_name, current_lines, current_structural
        if current_name is not None:
            blocks.setdefault(current_name, []).append("\n".join(current_lines))
            if current_structural:
                structural.add(current_name)
        current_name = None
        current_lines = []
        current_structural = False

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
                current_structural = True
                continue

            head = re.split(r"\s|:", line, maxsplit=1)[0]
            if head and head not in KEYWORDS:
                flush()
                current_name = head
                current_lines = [line]
                current_structural = False
                continue

        if current_name is not None:
            current_lines.append(line)

    flush()

    declarations: list[Declaration] = []
    dedicated_law_surface = is_dedicated_law_surface(path)
    quarantine_path = is_quarantine_path(path)
    for name, chunks in sorted(blocks.items()):
        merged = "\n".join(chunks)
        base_law_like = dedicated_law_surface or is_law_like(name)
        refinement_extra = contains_any(merged, REFINEMENT_MARKERS) and not contains_any(merged, STRICT_MARKERS)
        law_like = base_law_like or refinement_extra
        strict = base_law_like and (quarantine_path or contains_any(merged, STRICT_MARKERS))
        refinement = refinement_extra or (base_law_like and not strict)
        declarations.append(
            Declaration(
                name=name,
                text=merged,
                structural=name in structural,
                law_like=law_like,
                refinement=refinement,
                strict=strict,
            )
        )
    return declarations


def score_opportunity(path: Path, declarations: list[Declaration]) -> Opportunity | None:
    rel_path = rel(path)

    if any(Path(part).stem in OPPORTUNITY_EXCLUDE_PARTS for part in path.parts):
        return None
    if any(fragment in rel_path for fragment in OPPORTUNITY_EXCLUDE_NAME_FRAGMENTS):
        return None
    if is_quarantine_path(path):
        return None
    if any(decl.refinement for decl in declarations):
        return None
    structural = [decl.name for decl in declarations if decl.structural]
    decl_names = [decl.name for decl in declarations]
    if any(decl.law_like for decl in declarations):
        return None
    if not structural:
        return None
    if len(decl_names) < 6:
        return None

    score = 0
    reasons: list[str] = []

    score += min(len(decl_names), 12)
    reasons.append(f"{len(decl_names)} top-level declarations")

    score += 3 * len(structural)
    reasons.append(f"{len(structural)} structural declaration(s)")

    if rel_path.startswith("LogOS/LT/"):
        score += 6
        reasons.append("core LT module")
    elif rel_path.startswith("LogOS/Ports/"):
        score += 5
        reasons.append("port/module surface")
    elif rel_path.startswith("LogOS/Apps/LogicArchitecture/"):
        score += 4
        reasons.append("metatheory/application basis")

    for token in ("Kernel", "Stack", "Functor", "Port", "Boundary", "Architecture", "View", "Core"):
        if token in rel_path:
            score += 1
            reasons.append(f"path mentions {token}")

    return Opportunity(
        path=path,
        score=score,
        structural=structural,
        declarations=decl_names[:12],
        reasons=reasons,
    )


def main() -> int:
    try:
        thresholds = load_thresholds(THRESHOLDS)
    except RuntimeError as exc:
        print("law-surface-check: FAIL", file=sys.stderr)
        print(f"  - {exc}", file=sys.stderr)
        return 1

    if not LOGOS_DIR.is_dir():
        print("law-surface-check: FAIL", file=sys.stderr)
        print("  - missing LogOS directory", file=sys.stderr)
        return 1

    files = sorted(path for path in LOGOS_DIR.rglob("*.agda") if "_build" not in path.parts)
    module_stats = {path: extract_module_stats(path) for path in files}
    refinement_modules: list[Path] = []
    strict_modules: list[Path] = []
    strict_default_lane_modules: list[Path] = []
    opportunities: list[Opportunity] = []
    refinement_declarations: list[tuple[Path, Declaration]] = []
    strict_declarations: list[tuple[Path, Declaration]] = []
    strict_default_lane_declarations: list[tuple[Path, Declaration]] = []

    for path, declarations in module_stats.items():
        if any(decl.refinement for decl in declarations):
            refinement_modules.append(path)
            refinement_declarations.extend((path, decl) for decl in declarations if decl.refinement)
        if any(decl.strict for decl in declarations):
            strict_modules.append(path)
            strict_declarations.extend((path, decl) for decl in declarations if decl.strict)
            if not is_quarantine_path(path):
                strict_default_lane_modules.append(path)
                strict_default_lane_declarations.extend((path, decl) for decl in declarations if decl.strict)
        opp = score_opportunity(path, declarations)
        if opp is not None:
            opportunities.append(opp)

    opportunities.sort(key=lambda opp: (-opp.score, rel(opp.path)))

    total_modules = len(files)
    total_loc = count_loc(files)

    refinement_module_pct = 100.0 if total_modules == 0 else 100.0 * len(refinement_modules) / total_modules
    refinement_loc = count_loc(refinement_modules)
    refinement_declaration_count = len(refinement_declarations)

    strict_loc = count_loc(strict_modules)
    strict_declaration_count = len(strict_declarations)
    strict_default_lane_loc = count_loc(strict_default_lane_modules)
    strict_default_lane_declaration_count = len(strict_default_lane_declarations)
    total_loc = count_loc(files)

    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(
        json.dumps(
            {
                "heuristic": {
                    "fragments": list(LAW_FRAGMENTS),
                    "refinement_markers": list(REFINEMENT_MARKERS),
                    "strict_markers": list(STRICT_MARKERS),
                    "note": (
                        "Heuristic law-surface partition based on top-level declaration naming, "
                        "module role, and visible refinement/strict markers; use as a regression "
                        "signal, not a semantic completeness theorem."
                    ),
                },
                "totals": {
                    "modules": total_modules,
                    "loc": total_loc,
                },
                "refinement": {
                    "modules": len(refinement_modules),
                    "module_percent": round(refinement_module_pct, 4),
                    "loc": refinement_loc,
                    "declarations": refinement_declaration_count,
                },
                "strict": {
                    "modules": len(strict_modules),
                    "loc": strict_loc,
                    "declarations": strict_declaration_count,
                    "default_lane_modules": len(strict_default_lane_modules),
                    "default_lane_loc": strict_default_lane_loc,
                    "default_lane_declarations": strict_default_lane_declaration_count,
                    "quarantined_modules": len(strict_modules) - len(strict_default_lane_modules),
                    "quarantined_declarations": strict_declaration_count - strict_default_lane_declaration_count,
                },
                "thresholds": {
                    "refinement_law_modules_floor": thresholds.refinement_law_modules,
                    "refinement_law_module_pct_floor": thresholds.refinement_law_module_pct,
                    "refinement_law_declarations_floor": thresholds.refinement_law_declarations,
                    "strict_default_lane_modules_floor": thresholds.strict_default_lane_modules,
                    "strict_default_lane_declarations_floor": thresholds.strict_default_lane_declarations,
                },
                "sample_refinement_modules": [
                    {
                        "module": rel(path),
                        "declarations": [decl.name for decl in declarations if decl.refinement],
                    }
                    for path, declarations in [
                        (path, module_stats[path]) for path in refinement_modules[:50]
                    ]
                ],
                "sample_strict_default_lane_modules": [
                    {
                        "module": rel(path),
                        "declarations": [decl.name for decl in declarations if decl.strict],
                    }
                    for path, declarations in [
                        (path, module_stats[path]) for path in strict_default_lane_modules[:50]
                    ]
                ],
                "law_opportunities": [
                    {
                        "module": rel(opp.path),
                        "score": opp.score,
                        "structural": opp.structural,
                        "sample_declarations": opp.declarations,
                        "reasons": opp.reasons,
                    }
                    for opp in opportunities[:30]
                ],
            },
            indent=2,
            sort_keys=True,
        )
        + "\n",
        encoding="utf-8",
    )

    violations: list[str] = []
    if len(refinement_modules) < thresholds.refinement_law_modules:
        violations.append(
            "refinement law-bearing module count below floor"
            f" ({len(refinement_modules)} < {thresholds.refinement_law_modules})"
        )
    if refinement_module_pct + 1e-9 < thresholds.refinement_law_module_pct:
        violations.append(
            "refinement law-bearing module percentage below floor"
            f" ({refinement_module_pct:.2f}% < {thresholds.refinement_law_module_pct:.2f}%)"
        )
    if refinement_declaration_count < thresholds.refinement_law_declarations:
        violations.append(
            "refinement law declaration count below floor"
            f" ({refinement_declaration_count} < {thresholds.refinement_law_declarations})"
        )
    if len(strict_default_lane_modules) > thresholds.strict_default_lane_modules:
        violations.append(
            "strict law modules leaked into default lanes"
            f" ({len(strict_default_lane_modules)} > {thresholds.strict_default_lane_modules})"
        )
    if strict_default_lane_declaration_count > thresholds.strict_default_lane_declarations:
        violations.append(
            "strict law declarations leaked into default lanes"
            f" ({strict_default_lane_declaration_count} > {thresholds.strict_default_lane_declarations})"
        )

    if violations:
        print("law-surface-check: FAIL", file=sys.stderr)
        for violation in violations:
            print(f"  - {violation}", file=sys.stderr)
        print(f"  - report written to {rel(OUT)}", file=sys.stderr)
        return 1

    print("law-surface-check: OK")
    print(
        "  refinement law-bearing modules:"
        f" {len(refinement_modules)}/{total_modules}"
        f" ({refinement_module_pct:.2f}%)"
    )
    print(f"  refinement law declarations: {refinement_declaration_count}")
    print(f"  LOC in refinement law-bearing modules: {refinement_loc}/{total_loc}")
    print(
        "  strict-law quarantine:"
        f" {len(strict_modules)} modules,"
        f" {strict_declaration_count} declarations"
        f" ({len(strict_default_lane_modules)} default-lane modules,"
        f" {strict_default_lane_declaration_count} default-lane declarations)"
    )
    print(
        "  floors:"
        f" {thresholds.refinement_law_modules} refinement modules,"
        f" {thresholds.refinement_law_module_pct:.2f}% refinement modules,"
        f" {thresholds.refinement_law_declarations} refinement declarations,"
        f" {thresholds.strict_default_lane_modules} default-lane strict modules,"
        f" {thresholds.strict_default_lane_declarations} default-lane strict declarations"
    )
    if opportunities:
        print("  law-opportunity shortlist:")
        for opp in opportunities[:8]:
            print(
                "    -"
                f" {rel(opp.path)}"
                f" [score {opp.score}]"
                f" structural={', '.join(opp.structural[:3])}"
            )
    print(f"  report: {rel(OUT)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
PY
