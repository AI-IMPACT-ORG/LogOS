#!/usr/bin/env bash
# LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
# Copyright (C) 2026 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only
# Policy:
# - Curated default LT/API surfaces must not export `≡`-valued declarations.
# - Equality exports belong only in `Strictification`, `Definitional`, `Prelude`,
#   or executable `Checks` lanes.

set -euo pipefail

CHECK_NAME="equality-quarantine-check"
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
# shellcheck source=scripts/lib/check_common.sh
source "${SCRIPT_DIR}/lib/check_common.sh"

die() { check_die "${CHECK_NAME}" "$*"; }

ROOT="$(check_repo_root "${BASH_SOURCE[0]}")"
cd "${ROOT}"

check_require_cmd "${CHECK_NAME}" python3

python3 - <<'PY'
from __future__ import annotations

import sys
from pathlib import Path

ROOT = Path(".").resolve()

SURFACES = [
    "LogOS/API/LT.agda",
    "LogOS/API/Kernel.agda",
    "LogOS/API/Guarded.agda",
    "LogOS/API/Architecture.agda",
    "LogOS/API/Theorems.agda",
    "LogOS/API/Theorems/Core.agda",
    "LogOS/LT/Coherence.agda",
    "LogOS/LT/Hom.agda",
    "LogOS/LT/Hom/Core.agda",
    "LogOS/LT/Hom/Coercions.agda",
    "LogOS/LT/Kernel.agda",
    "LogOS/LT/TypeTheory.agda",
    "LogOS/LT/TypeTheory/Surface.agda",
    "LogOS/LT/Theorems/ArchitecturalNormalForm.agda",
]

SKIP_PREFIXES = ("module ", "open ", "import ", "record ", "data ", "private", "mutual", "where", "infix", "{-", "--")


def is_top_level_name(line: str) -> bool:
    if not line or line[:1].isspace():
        return False
    stripped = line.strip()
    if not stripped or any(stripped.startswith(p) for p in SKIP_PREFIXES):
        return False
    if ":" in stripped or "=" in stripped or " " in stripped or "\t" in stripped:
        return False
    if stripped == "_":
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


violations: list[str] = []

for rel in SURFACES:
    path = ROOT / rel
    if not path.is_file():
        violations.append(f"{rel}: missing curated surface file")
        continue
    lines = path.read_text(encoding="utf-8").splitlines()
    idx = 0
    while idx < len(lines):
        line = lines[idx]
        if not is_top_level_name(line):
            idx += 1
            continue
        symbol = line.strip()
        next_idx = next_nonempty(lines, idx + 1)
        if next_idx is None or not lines[next_idx].lstrip().startswith(":"):
            idx += 1
            continue
        type_block, end_idx = collect_type_block(lines, next_idx)
        if "≡" in type_block:
            violations.append(f"{rel}:{idx + 1}: curated surface exports equality-valued declaration {symbol}")
        idx = end_idx

if violations:
    print("equality-quarantine-check: FAIL", file=sys.stderr)
    for item in violations:
        print(f"  - {item}", file=sys.stderr)
    raise SystemExit(1)

print("equality-quarantine-check: OK")
PY
