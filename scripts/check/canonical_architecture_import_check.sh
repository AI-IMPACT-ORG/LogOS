#!/usr/bin/env bash
# LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
# Copyright (C) 2026 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only
# Policy:
# - Canonical architecture/implementation modules may not depend on compatibility
#   shims.
# - Canonical LT/Ports internals should import the pristine `Core` lane directly
#   when a façade wrapper exists, except at explicitly curated façade surfaces.

set -euo pipefail

CHECK_NAME="canonical-architecture-import-check"
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

IMPORT_RE = re.compile(r"^\s*(?:open\s+import|import)\s+([A-Za-z0-9_.']+)\b")

SHIM_MODULES = {
    "LogOS.LT.CodeCompat",
    "LogOS.LT.LOG.Realiser2Cat",
    "LogOS.LT.LOG.RealiserContract2Cat",
    "LogOS.LT.LOG.RealiserFlow2Cat",
    "LogOS.LT.LOG.RealiserDecode2Cat",
    "LogOS.LT.LOG.EncodePort2CatG",
    "LogOS.LT.LOG.QuotePort2CatG",
    "LogOS.LT.LOG.QuotePort2CatG.Displayed",
    "LogOS.LT.LOG.FlowContract2CatG",
    "LogOS.LT.LOG.BulkBoundary2CatG",
    "LogOS.LT.LOG.BulkBoundaryContract2CatG",
    "LogOS.API.Ports.LTDecorationsLOGG",
    "LogOS.API.Ports.UniversalityLOGG",
    "LogOS.Ports.Universality.BudgetBus2CatG",
    "LogOS.Ports.Universality.FlowBudget2CatG",
}

FACADE_MODULES = {
    "LogOS.LT.BoundaryImplementation",
    "LogOS.LT.Hom",
    "LogOS.LT.LOG.Implementation2Cat",
    "LogOS.LT.LOG.ImplementationContract2Cat",
    "LogOS.LT.LOG.ImplementationFlow2Cat",
    "LogOS.LT.LOG.ImplementationDecode2Cat",
}

FACADE_IMPORT_PATHS = {
    "LogOS/API/Kernel.agda",
    "LogOS/LT/LOG/Discipline/PortsAsDisplayed.agda",
}

scan_roots = [
    ROOT / "LogOS" / "LT",
    ROOT / "LogOS" / "Ports",
    ROOT / "LogOS" / "API" / "Kernel.agda",
    ROOT / "LogOS" / "API" / "Ports" / "LTDecorationsArchitecture.agda",
    ROOT / "LogOS" / "API" / "Ports" / "UniversalityArchitecture.agda",
]

violations: list[str] = []

def iter_files() -> list[Path]:
    out: list[Path] = []
    for root in scan_roots:
        if root.is_dir():
            out.extend(sorted(p for p in root.rglob("*.agda") if "_build" not in p.parts))
        elif root.is_file():
            out.append(root)
    return out

for path in iter_files():
    rel = path.relative_to(ROOT).as_posix()
    for i, line in enumerate(path.read_text(encoding="utf-8").splitlines(), start=1):
        m = IMPORT_RE.match(line)
        if not m:
            continue
        dep = m.group(1)
        if dep in SHIM_MODULES:
            violations.append(f"{rel}:{i}: imports compatibility shim {dep}")
        if dep in FACADE_MODULES and rel not in FACADE_IMPORT_PATHS:
            violations.append(f"{rel}:{i}: imports façade wrapper {dep} instead of its Core module")

if violations:
    print("canonical-architecture-import-check: FAIL", file=sys.stderr)
    print("Policy: canonical architecture modules must import canonical/Core names directly.", file=sys.stderr)
    for v in violations:
        print(f"  - {v}", file=sys.stderr)
    raise SystemExit(1)

print("canonical-architecture-import-check: OK")
PY
