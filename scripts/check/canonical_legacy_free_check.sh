#!/usr/bin/env bash
# LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
# Copyright (C) 2026 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only
# Policy:
# - Canonical architecture/implementation/law surfaces must be free of
#   retired legacy names.

set -euo pipefail

CHECK_NAME="canonical-legacy-free-check"
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
# shellcheck source=scripts/lib/check_common.sh
source "${SCRIPT_DIR}/lib/check_common.sh"

ROOT="$(check_repo_root "${BASH_SOURCE[0]}")"
cd "${ROOT}"

check_require_cmd "${CHECK_NAME}" python3

python3 - <<'PY'
from __future__ import annotations

import re
import sys
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

SCAN_ROOTS = [
    ROOT / "LogOS" / "LT",
    ROOT / "LogOS" / "Ports",
    ROOT / "LogOS" / "API",
    ROOT / "docs" / "Core" / "Spec" / "LogicalTransformers.lagda.md",
    ROOT / "docs" / "Core" / "Spec" / "LogOS_Specification.lagda.md",
]

violations: list[str] = []

for scan_root in SCAN_ROOTS:
    if scan_root.is_dir():
        paths = sorted(
            path for path in scan_root.rglob("*.agda")
            if "_build" not in path.parts and "Apps" not in path.parts
        )
    elif scan_root.is_file():
        paths = [scan_root]
    else:
        continue

    for path in paths:
        rel = path.relative_to(ROOT).as_posix()
        for i, line in enumerate(path.read_text(encoding="utf-8").splitlines(), start=1):
            for name in sorted(LEGACY_IDENTIFIERS):
                if re.search(rf"\b{re.escape(name)}\b", line):
                    violations.append(f"{rel}:{i}: {name}")
            for name in sorted(LEGACY_MODULES):
                if re.search(rf"\b{re.escape(name)}\b", line):
                    violations.append(f"{rel}:{i}: {name}")

if violations:
    print("canonical-legacy-free-check: FAIL", file=sys.stderr)
    print("Policy: canonical lanes must not mention transition-only legacy names.", file=sys.stderr)
    for violation in violations:
        print(f"  - {violation}", file=sys.stderr)
    raise SystemExit(1)

print("canonical-legacy-free-check: OK")
PY
