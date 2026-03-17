#!/usr/bin/env bash
# LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
# Copyright (C) 2026 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only
# Policy:
# - Retired architecture names are tracked after shim removal.
# - This check is inventory-only: it reports residual occurrences in canonical
#   and integration lanes, but does not fail CI.

set -euo pipefail

CHECK_NAME="legacy-architecture-name-check"
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
# shellcheck source=scripts/lib/check_common.sh
source "${SCRIPT_DIR}/lib/check_common.sh"

ROOT="$(check_repo_root "${BASH_SOURCE[0]}")"
cd "${ROOT}"

check_require_cmd "${CHECK_NAME}" python3

python3 - <<'PY'
from __future__ import annotations

import re
from pathlib import Path

ROOT = Path(".").resolve()

LEGACY_IDENTIFIERS = {
    "CodeCompat",
    "RealiserDisplayed",
    "RealiserTag",
    "forgetRealiser",
    "RealiserContractStack",
    "RealiserContractKernel",
    "RealiserFlowStack",
    "realiserSig",
    "realiserSingleton",
    "LTDecorationsLOGG",
    "UniversalityLOGG",
}

LEGACY_MODULES = {
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

SCAN_DIRS = [
    ROOT / "LogOS",
    ROOT / "docs" / "Core" / "Spec",
]


def lane_for(rel: str) -> str:
    if rel.startswith("LogOS/Apps/"):
        return "integration"
    return "canonical"


hits: dict[str, list[str]] = {
    "canonical": [],
    "integration": [],
}

for scan_dir in SCAN_DIRS:
    if not scan_dir.exists():
        continue
    for path in sorted(scan_dir.rglob("*")):
        if path.suffix not in {".agda", ".md"}:
            continue
        if "_build" in path.parts:
            continue
        rel = path.relative_to(ROOT).as_posix()
        lane = lane_for(rel)
        for i, line in enumerate(path.read_text(encoding="utf-8").splitlines(), start=1):
            for name in sorted(LEGACY_IDENTIFIERS):
                if re.search(rf"\b{re.escape(name)}\b", line):
                    hits[lane].append(f"{rel}:{i}: {name}")
            for name in sorted(LEGACY_MODULES):
                if re.search(rf"\b{re.escape(name)}\b", line):
                    hits[lane].append(f"{rel}:{i}: {name}")

print("legacy-architecture-name-check: inventory (non-failing)")
for lane in ("canonical", "integration"):
    lane_hits = hits[lane]
    print(f"  {lane}: {len(lane_hits)}")
    for hit in lane_hits[:40]:
        print(f"    - {hit}")
    if len(lane_hits) > 40:
        print(f"    - ... {len(lane_hits) - 40} more")
PY
