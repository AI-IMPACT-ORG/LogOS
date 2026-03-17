#!/usr/bin/env bash
# LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
# Copyright (C) 2026 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only
# Policy:
# - The curated LT/API surfaces are refinement-first.
# - Strict/equality surfaces must stay behind explicit `Strictification`,
#   `Definitional`, or `Shadowing` lanes.

set -euo pipefail

CHECK_NAME="refinement-first-surface-check"
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

SURFACES = [
    "LogOS/API/LT.agda",
    "LogOS/API/Kernel.agda",
    "LogOS/API/Guarded.agda",
    "LogOS/API/Architecture.agda",
    "LogOS/API/Theorems.agda",
    "LogOS/API/Theorems/Core.agda",
    "LogOS/LT/Coherence.agda",
    "LogOS/LT/Hom.agda",
    "LogOS/LT/Hom/Core.agda",
    "LogOS/LT/Hom/Coercions.agda",
    "LogOS/LT/Kernel.agda",
    "LogOS/LT/TypeTheory.agda",
    "LogOS/LT/TypeTheory/Surface.agda",
    "LogOS/LT/Theorems/ArchitecturalNormalForm.agda",
]

IMPORT_RE = re.compile(r"^\s*(?:open\s+import|import)\s+([A-Za-z0-9_.']+)\b")
FORBIDDEN_IMPORTS = {
    "LogOS.API.Strictification",
    "LogOS.API.Theorems.Strictification",
    "LogOS.API.Ports.LTStrictificationLOG",
    "LogOS.LT.Strictification.Coherence",
    "LogOS.LT.Hom.Strictification",
    "LogOS.LT.TypeTheory.Strictification",
    "LogOS.LT.Theorems.ArchitecturalNormalFormStrictification",
    "LogOS.LT.Discipline.ArchitectureImplementationLaw.Strictification",
    "LogOS.LT.LOG.ClassicalLimit2Cat",
    "LogOS.LT.LOG.StrictDecode2Cat",
    "LogOS.LT.Ports.PortSigStrictification",
    "LogOS.LT.Ports.PortStack.ClassicalLimit",
    "LogOS.LT.Ports.PortStack.Raw",
    "LogOS.Ports.ClassicalLimit",
}
FORBIDDEN_TOKENS = (
    "KernelHom≡",
    "StrictKernelHom",
    "decode-mapCode≡",
    "Tm≡",
    "strict→under",
    "toFacadeHom-fromFacadeHom≡id",
    "fromFacadeHom-toFacadeHom≡id",
    "strictifyDisplayed",
    "strictifyStack",
)

violations: list[str] = []

for rel in SURFACES:
    path = ROOT / rel
    if not path.is_file():
        violations.append(f"{rel}: missing curated surface file")
        continue
    lines = path.read_text(encoding="utf-8").splitlines()
    for i, line in enumerate(lines, start=1):
        m = IMPORT_RE.match(line)
        if m and m.group(1) in FORBIDDEN_IMPORTS:
            violations.append(f"{rel}:{i}: imports quarantined strict/equality surface {m.group(1)}")
        for token in FORBIDDEN_TOKENS:
            if token in line:
                violations.append(f"{rel}:{i}: mentions strict/equality-only token {token}")

if violations:
    print("refinement-first-surface-check: FAIL", file=sys.stderr)
    print(
        "Policy: curated LT/API surfaces remain refinement-only; strict/equality material belongs in explicit Strictification/Definitional/Shadowing lanes.",
        file=sys.stderr,
    )
    for item in violations:
        print(f"  - {item}", file=sys.stderr)
    raise SystemExit(1)

print("refinement-first-surface-check: OK")
PY
