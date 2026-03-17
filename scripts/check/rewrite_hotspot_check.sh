#!/usr/bin/env bash
# LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
# Copyright (C) 2026 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only
# Policy:
# - `rewrite` is banned in the main semantic hotspots where relation-valued helper
#   lemmas should carry the proof burden.
# - In the ZFC semantics core, any remaining `rewrite` must be explicitly marked
#   with `-- rewrite-justified:<lemma-name>`.

set -euo pipefail

CHECK_NAME="rewrite-hotspot-check"
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

FORBIDDEN_FILES = [
    ROOT / "LogOS" / "Apps" / "TuringCategory" / "PartialMaps" / "Core.agda",
    ROOT / "LogOS" / "Ports" / "Valuation" / "QAdapterBudgetTransport.agda",
]

ZFC_DIR = ROOT / "LogOS" / "Apps" / "ZFC" / "Proof" / "Semantics" / "Core"
REWRITE_RE = re.compile(r"\brewrite\b")
JUSTIFIED_RE = re.compile(r"--\s*rewrite-justified:[A-Za-z0-9_.-]+")

violations: list[str] = []

for path in FORBIDDEN_FILES:
    if not path.is_file():
        violations.append(f"missing forbidden-rewrite target: {path.relative_to(ROOT).as_posix()}")
        continue
    for i, line in enumerate(path.read_text(encoding="utf-8").splitlines(), start=1):
        if REWRITE_RE.search(line):
            violations.append(f"{path.relative_to(ROOT).as_posix()}:{i}: rewrite is forbidden in this hotspot")

if ZFC_DIR.is_dir():
    for path in sorted(ZFC_DIR.rglob("*.agda")):
        rel = path.relative_to(ROOT).as_posix()
        for i, line in enumerate(path.read_text(encoding="utf-8").splitlines(), start=1):
            if not REWRITE_RE.search(line):
                continue
            if not JUSTIFIED_RE.search(line):
                violations.append(f"{rel}:{i}: rewrite in ZFC semantics core requires -- rewrite-justified:<lemma-name>")

if violations:
    print("rewrite-hotspot-check: FAIL", file=sys.stderr)
    for item in violations:
        print(f"  - {item}", file=sys.stderr)
    raise SystemExit(1)

print("rewrite-hotspot-check: OK")
PY
