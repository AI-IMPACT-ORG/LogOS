#!/usr/bin/env bash
# LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
# Copyright (C) 2026 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only
# Policy:
# - Independent port composition must use `ProductDisplayed`.
# - Avoid hand-rolled displayed products (a common drift anti-pattern). If a manual product is truly required,
#   add a local justification marker `MANUAL-PRODUCT-JUSTIFICATION:` in the file.

set -euo pipefail

CHECK_NAME="no-manual-displayed-product-check"
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

files: list[Path] = []
log_dir = ROOT / "LogOS" / "LT" / "LOG"
ports_dir = ROOT / "LogOS" / "Ports"

if log_dir.is_dir():
    files += sorted(log_dir.glob("*2Cat.agda"))
if ports_dir.is_dir():
    files += sorted(ports_dir.rglob("*2Cat.agda"))

ob_prod = re.compile(r"\bOb\s*=\s*λ\b[\s\S]{0,200}×")
homd_prod = re.compile(r"\bHomD\s*=\s*λ\b[\s\S]{0,200}×")

violations: list[str] = []
for p in files:
    text = p.read_text(encoding="utf-8")

    if "MANUAL-PRODUCT-JUSTIFICATION:" in text:
        continue

    # If it already uses the canonical constructor, it's fine.
    if "ProductDisplayed" in text:
        continue

    # Heuristic: a hand-rolled displayed product usually uses a product in both Ob and HomD.
    if ob_prod.search(text) and homd_prod.search(text):
        violations.append(str(p.relative_to(ROOT)))

if violations:
    print("no-manual-displayed-product-check: FAIL", file=sys.stderr)
    print("manual displayed products detected in `*2Cat.agda` modules:", file=sys.stderr)
    for v in violations:
        print(f"  - {v}", file=sys.stderr)
    print("", file=sys.stderr)
    print("Fix: use `ProductDisplayed`, or add `MANUAL-PRODUCT-JUSTIFICATION:` in the file.", file=sys.stderr)
    sys.exit(1)

print("no-manual-displayed-product-check: OK")
PY

