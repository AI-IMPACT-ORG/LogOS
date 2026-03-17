#!/usr/bin/env bash
# LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
# Copyright (C) 2026 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only
# Policy:
# - Legacy architecture/implementation/law shim module paths have been retired.
# - Reintroducing any old-name shim requires an explicit policy change first.

set -euo pipefail

CHECK_NAME="architecture-shim-check"
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
# shellcheck source=scripts/lib/check_common.sh
source "${SCRIPT_DIR}/lib/check_common.sh"

die() { check_die "${CHECK_NAME}" "$*"; }

ROOT="$(check_repo_root "${BASH_SOURCE[0]}")"
cd "${ROOT}"

python3 - <<'PY'
from __future__ import annotations

import sys
from pathlib import Path

ROOT = Path(".").resolve()

RETIRED_SHIMS = [
    "LogOS/LT/CodeCompat.agda",
    "LogOS/LT/LOG/Realiser2Cat.agda",
    "LogOS/LT/LOG/RealiserContract2Cat.agda",
    "LogOS/LT/LOG/RealiserFlow2Cat.agda",
    "LogOS/LT/LOG/RealiserDecode2Cat.agda",
    "LogOS/LT/LOG/EncodePort2CatG.agda",
    "LogOS/LT/LOG/QuotePort2CatG.agda",
    "LogOS/LT/LOG/QuotePort2CatG/Displayed.agda",
    "LogOS/LT/LOG/FlowContract2CatG.agda",
    "LogOS/LT/LOG/BulkBoundary2CatG.agda",
    "LogOS/LT/LOG/BulkBoundaryContract2CatG.agda",
    "LogOS/LT/LOG/Discipline/PortsAsDisplayedCompatibility.agda",
    "LogOS/API/Ports/LTDecorationsLOGG.agda",
    "LogOS/API/Ports/UniversalityLOGG.agda",
    "LogOS/Ports/Universality/BudgetBus2CatG.agda",
    "LogOS/Ports/Universality/FlowBudget2CatG.agda",
    "LogOS/Ports/Discipline/PortsAsDisplayedCompatibility.agda",
]

present = [rel for rel in RETIRED_SHIMS if (ROOT / rel).exists()]

if present:
    print("architecture-shim-check: FAIL", file=sys.stderr)
    print("Policy: retired legacy shim modules must remain absent.", file=sys.stderr)
    for rel in present:
        print(f"  - {rel}", file=sys.stderr)
    raise SystemExit(1)

print("architecture-shim-check: OK")
PY
