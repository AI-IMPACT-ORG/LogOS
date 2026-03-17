#!/usr/bin/env bash
# LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
# Copyright (C) 2026 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only
# Policy:
# - Large maintained subtrees must expose a local navigator.
# - For directories under `LogOS/API`, `LogOS/Checks`, `LogOS/LT`,
#   `LogOS/Ports`, and `LogOS/Apps`, a directory with at least 8 direct Agda
#   files must contain either a sibling README or a local `All` navigator module.

set -euo pipefail

CHECK_NAME="subtree-navigator-check"
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
SCAN_ROOTS = [
    ROOT / "LogOS" / "API",
    ROOT / "LogOS" / "Checks",
    ROOT / "LogOS" / "LT",
    ROOT / "LogOS" / "Ports",
    ROOT / "LogOS" / "Apps",
]

violations: list[str] = []

for scan_root in SCAN_ROOTS:
    if not scan_root.is_dir():
        continue
    dirs = [scan_root]
    dirs.extend(sorted(p for p in scan_root.rglob("*") if p.is_dir()))
    for path in dirs:
        direct_agda = sorted(
            child for child in path.iterdir()
            if child.is_file() and child.suffix == ".agda"
        )
        if len(direct_agda) < 8:
            continue
        if (path / "README.md").is_file() or (path / "All.agda").is_file():
            continue
        violations.append(
            f"{path.relative_to(ROOT).as_posix()}: {len(direct_agda)} direct .agda files but no README.md or All.agda"
        )

if violations:
    print("subtree-navigator-check: FAIL", file=sys.stderr)
    print("Policy: substantial maintained subtrees need a local navigator.", file=sys.stderr)
    for item in violations:
        print(f"  - {item}", file=sys.stderr)
    raise SystemExit(1)

print("subtree-navigator-check: OK")
PY
