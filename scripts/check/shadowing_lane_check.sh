#!/usr/bin/env bash
# LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
# Copyright (C) 2026 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only
# Policy:
# - `LogOS.LT.Ports.PortStack.Raw` is an explicit raw/internal lane.
# - Docs, curated API modules, and app surfaces must not import it directly.

set -euo pipefail

CHECK_NAME="shadowing-lane-check"
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
SCAN_ROOTS = [ROOT / "docs", ROOT / "LogOS" / "API", ROOT / "LogOS" / "Apps"]
EXCLUDED = {
    ROOT / "docs" / "Core" / "Spec" / "LogicalTransformers.lagda.md",
}
IMPORT_RE = re.compile(r"^\s*(?:open\s+import|import)\s+(LogOS\.LT\.Ports\.PortStack\.Shadowing)\b")

violations: list[str] = []

for scan_root in SCAN_ROOTS:
    if not scan_root.exists():
        continue
    for path in sorted(scan_root.rglob("*")):
        if not path.is_file():
            continue
        if path in EXCLUDED or "Generated" in path.parts:
            continue
        if path.suffix not in {".agda", ".md"} and not path.name.endswith(".lagda.md"):
            continue
        for i, line in enumerate(path.read_text(encoding="utf-8").splitlines(), start=1):
            if IMPORT_RE.match(line):
                rel = path.relative_to(ROOT).as_posix()
                violations.append(f"{rel}:{i}")

if violations:
    print("shadowing-lane-check: FAIL", file=sys.stderr)
    for item in violations:
        print(f"  - {item}: direct Shadowing import is forbidden on docs/API/app surfaces", file=sys.stderr)
    raise SystemExit(1)

print("shadowing-lane-check: OK")
PY
