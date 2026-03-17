#!/usr/bin/env bash
# LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
# Copyright (C) 2026 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only
# Policy:
# - High-risk public theorem surfaces must declare relation status explicitly.
# - New `_≈_`, `_⊑_`, `_≼_`, `_≤s_`, and `≡` theorem results in covered modules must be
#   manifest-listed before they land.
# - Canonical theorem names must end with a suffix matching their relation mode.

set -euo pipefail

CHECK_NAME="relation-status-naming-check"
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
# shellcheck source=scripts/lib/check_common.sh
source "${SCRIPT_DIR}/lib/check_common.sh"

die() { check_die "${CHECK_NAME}" "$*"; }

ROOT="$(check_repo_root "${BASH_SOURCE[0]}")"
cd "${ROOT}"

check_require_cmd "${CHECK_NAME}" python3

python3 - <<'PY'
from __future__ import annotations

import re
import sys
from pathlib import Path

ROOT = Path(".").resolve()
MANIFEST = ROOT / "scripts" / "relation_status_manifest.tsv"

COVERED_FILES = [
    ROOT / "LogOS" / "LT" / "Flow.agda",
    ROOT / "LogOS" / "LT" / "Reflection.agda",
    ROOT / "LogOS" / "Ports" / "BoundaryTransparency.agda",
    ROOT / "LogOS" / "Ports" / "BoundaryTransparency" / "Definitional.agda",
    ROOT / "LogOS" / "Apps" / "TuringCategory" / "PartialMaps" / "Core.agda",
    ROOT / "LogOS" / "Apps" / "LogicArchitecture" / "MetaTheory" / "Basis" / "ObservationReflection" / "Core.agda",
    ROOT / "LogOS" / "Apps" / "LogicArchitecture" / "MetaTheory" / "Basis" / "ObservationReflection" / "Definitional.agda",
    ROOT / "LogOS" / "Ports" / "Valuation" / "QAdapterBudgetTransport.agda",
]

SKIP_PREFIXES = (
    "module ",
    "open ",
    "import ",
    "record ",
    "data ",
    "private",
    "mutual",
    "where",
    "infix",
    "{-",
    "--",
)


def module_from_path(path: Path) -> str:
    rel = path.relative_to(ROOT).as_posix()
    assert rel.endswith(".agda")
    return rel[:-5].replace("/", ".")


def is_top_level_name(line: str) -> bool:
    if not line or line[:1].isspace():
        return False
    stripped = line.strip()
    if not stripped or any(stripped.startswith(p) for p in SKIP_PREFIXES):
        return False
    if ":" in stripped or "=" in stripped:
        return False
    if " " in stripped or "\t" in stripped:
        return False
    return True


def next_nonempty(lines: list[str], start: int) -> int | None:
    for idx in range(start, len(lines)):
        if lines[idx].strip():
            return idx
    return None


def collect_type_block(lines: list[str], colon_idx: int) -> tuple[str, int]:
    block: list[str] = []
    idx = colon_idx
    while idx < len(lines):
        line = lines[idx]
        if idx > colon_idx and line and not line[:1].isspace() and not line.lstrip().startswith(":"):
            break
        block.append(line)
        idx += 1
    return "\n".join(block), idx


def normalize_type(block: str) -> str:
    parts: list[str] = []
    for raw in block.splitlines():
        line = raw.split("--", 1)[0].strip()
        if line:
            parts.append(line)
    return " ".join(parts)


def classify_relation(type_text: str) -> str | None:
    result = type_text.rsplit("→", 1)[-1]
    if "_≈_" in result:
        return "approx"
    if "_⊑_" in result or "_≼_" in result or "_≤s_" in result:
        return "under"
    if "≡" in result:
        return "strict"
    return None


def suffix_ok(symbol: str, relation: str) -> bool:
    if relation == "approx":
        return symbol.endswith("≈") or symbol.endswith("Approx")
    if relation == "under":
        return symbol.endswith("⊑") or symbol.endswith("Le") or symbol.endswith("Monotone")
    if relation == "strict":
        return symbol.endswith("≡") or symbol.endswith("Strict") or symbol.endswith("Def")
    return False


manifest: dict[tuple[str, str], tuple[str, str]] = {}
manifest_lines: set[tuple[str, str]] = set()

if not MANIFEST.is_file():
    print(f"{MANIFEST.relative_to(ROOT)}: missing manifest", file=sys.stderr)
    raise SystemExit(1)

for i, raw in enumerate(MANIFEST.read_text(encoding="utf-8").splitlines(), start=1):
    line = raw.strip()
    if not line or line.startswith("#"):
        continue
    cols = raw.split("\t")
    if len(cols) != 4:
        print(f"{MANIFEST.relative_to(ROOT)}:{i}: expected 4 tab-separated columns", file=sys.stderr)
        raise SystemExit(1)
    module_name, symbol, relation, status = cols
    if relation not in {"approx", "under", "strict"}:
        print(f"{MANIFEST.relative_to(ROOT)}:{i}: invalid relation {relation!r}", file=sys.stderr)
        raise SystemExit(1)
    if status not in {"canonical", "legacy-compatible"}:
        print(f"{MANIFEST.relative_to(ROOT)}:{i}: invalid status {status!r}", file=sys.stderr)
        raise SystemExit(1)
    key = (module_name, symbol)
    if key in manifest:
        print(f"{MANIFEST.relative_to(ROOT)}:{i}: duplicate manifest entry for {module_name}.{symbol}", file=sys.stderr)
        raise SystemExit(1)
    manifest[key] = (relation, status)
    manifest_lines.add(key)

violations: list[str] = []
seen: set[tuple[str, str]] = set()

for path in COVERED_FILES:
    if not path.is_file():
        violations.append(f"missing covered file: {path.relative_to(ROOT).as_posix()}")
        continue

    module_name = module_from_path(path)
    lines = path.read_text(encoding="utf-8").splitlines()
    idx = 0
    while idx < len(lines):
        line = lines[idx]
        if not is_top_level_name(line):
            idx += 1
            continue
        next_idx = next_nonempty(lines, idx + 1)
        if next_idx is None or not lines[next_idx].lstrip().startswith(":"):
            idx += 1
            continue

        symbol = line.strip()
        type_block, end_idx = collect_type_block(lines, next_idx)
        relation = classify_relation(normalize_type(type_block))
        if relation is not None:
            key = (module_name, symbol)
            seen.add(key)
            manifest_entry = manifest.get(key)
            if manifest_entry is None:
                violations.append(
                    f"{path.relative_to(ROOT).as_posix()}:{idx + 1}: relation-returning theorem not listed in manifest: {symbol} ({relation})"
                )
            else:
                manifest_relation, status = manifest_entry
                if manifest_relation != relation:
                    violations.append(
                        f"{path.relative_to(ROOT).as_posix()}:{idx + 1}: manifest says {manifest_relation} but signature classifies as {relation}: {symbol}"
                    )
                if status == "canonical" and not suffix_ok(symbol, relation):
                    violations.append(
                        f"{path.relative_to(ROOT).as_posix()}:{idx + 1}: canonical {relation} theorem lacks required suffix: {symbol}"
                    )
        idx = end_idx

for module_name, symbol in sorted(manifest_lines - seen):
    violations.append(f"manifest entry not found in covered files: {module_name}.{symbol}")

if violations:
    print("relation-status-naming-check: FAIL", file=sys.stderr)
    for item in violations:
        print(f"  - {item}", file=sys.stderr)
    raise SystemExit(1)

print("relation-status-naming-check: OK")
PY
