#!/usr/bin/env bash
# LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
# Copyright (C) 2026 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only
# Policy:
# - `QuoteConeMMP` is an internal implementation-lane name.
# - Public docs, checks, and curated API surfaces must use the centering-facing
#   vocabulary instead of surfacing the old packaging term.

set -euo pipefail

CHECK_NAME="centering-quote-vocabulary-check"
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
SCAN_ROOTS = [ROOT / "LogOS" / "API", ROOT / "LogOS" / "Checks", ROOT / "docs"]
EXCLUDED = {
    ROOT / "docs" / "Core" / "Spec" / "LogicalTransformers.lagda.md",
}

violations: list[str] = []

for scan_root in SCAN_ROOTS:
    if not scan_root.exists():
        continue
    for path in sorted(scan_root.rglob("*")):
        if not path.is_file():
            continue
        if path.suffix not in {".agda", ".md"} and not path.name.endswith(".lagda.md"):
            continue
        if path in EXCLUDED:
            continue
        if "Generated" in path.parts:
            continue
        text = path.read_text(encoding="utf-8")
        if "QuoteConeMMP" in text:
            rel = path.relative_to(ROOT).as_posix()
            violations.append(rel)

if violations:
    print("centering-quote-vocabulary-check: FAIL", file=sys.stderr)
    for rel in violations:
        print(f"  - {rel}: uses internal QuoteConeMMP vocabulary outside the implementation lane", file=sys.stderr)
    raise SystemExit(1)

print("centering-quote-vocabulary-check: OK")
PY
