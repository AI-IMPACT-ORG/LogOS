#!/usr/bin/env bash
# LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
# Copyright (C) 2026 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only
# Policy:
# - Core modules should not import `Definitional` or `Strictification` lanes
#   unless explicitly allowlisted.

set -euo pipefail

CHECK_NAME="core-role-check"
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
LOGOS_DIR = ROOT / "LogOS"
IMPORT_RE = re.compile(r"^\s*(?:open\s+import|import)\s+([A-Za-z0-9_.']+)\b", re.M)
ALLOWLIST = {
    "LogOS/LT/LOG/Kernel2Cat/Core.agda",
    "LogOS/Ports/Discipline/PortsAsDisplayed/Core.agda",
}


def rel(path: Path) -> str:
    return path.relative_to(ROOT).as_posix()


violations: list[str] = []

for path in sorted(LOGOS_DIR.rglob("Core.agda")):
    rel_path = rel(path)
    if rel_path in ALLOWLIST or "Checks" in path.parts:
        continue
    text = path.read_text(encoding="utf-8")
    imports = IMPORT_RE.findall(text)
    bad = sorted({mod for mod in imports if ".Definitional" in mod or ".Strictification" in mod})
    if bad:
        joined = ", ".join(bad)
        violations.append(f"{rel_path}: imports quarantine lanes ({joined})")

if violations:
    print("core-role-check: FAIL", file=sys.stderr)
    for item in violations:
        print(f"  - {item}", file=sys.stderr)
    raise SystemExit(1)

print("core-role-check: OK")
PY
