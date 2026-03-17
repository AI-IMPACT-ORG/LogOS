#!/usr/bin/env bash
# LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
# Copyright (C) 2026 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only
# Policy:
# - The canonical iterative-tree successor slice must stay free of same-stage
#   completion machinery.
# - In particular, `LogOS/Apps/ZFC/Models/IterativeSetTree/CumulativeHierarchy.agda`
#   must not import the one-stage completion assembler or re-expose
#   completion-layer names.

set -euo pipefail

CHECK_NAME="zfc-canonical-slice-purity-check"
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
TARGET = ROOT / "LogOS" / "Apps" / "ZFC" / "Models" / "IterativeSetTree" / "CumulativeHierarchy.agda"

if not TARGET.is_file():
    print("zfc-canonical-slice-purity-check: OK (target missing)")
    raise SystemExit(0)

text = TARGET.read_text(encoding="utf-8")
violations: list[str] = []

forbidden_imports = {
    "LogOS.Apps.ZFC.Models.IterativeSetTree.LateCollapse",
    "LogOS.Apps.ZFC.Models.IterativeSetTree.CumulativeHierarchyCompletion",
}

forbidden_identifiers = {
    "CurrentCompletion",
    "SuccessorCompletion",
    "currentCompletion",
    "successorCompletion",
    "CompleteCurrent",
    "CompleteSuccessor",
    "CompleteBoth",
}

import_re = re.compile(r"^\s*(?:open\s+import|import)\s+([A-Za-z0-9_.']+)\b", re.MULTILINE)

for mod in import_re.findall(text):
    if mod in forbidden_imports:
        violations.append(f"forbidden import: {mod}")

for name in sorted(forbidden_identifiers):
    if re.search(rf"\b{re.escape(name)}\b", text):
        violations.append(f"forbidden completion identifier in canonical slice: {name}")

if violations:
    print("zfc-canonical-slice-purity-check: FAIL", file=sys.stderr)
    print(
        "Policy: LogOS/Apps/ZFC/Models/IterativeSetTree/CumulativeHierarchy.agda must remain canonical-only.",
        file=sys.stderr,
    )
    for item in violations:
        print(f"  - {item}", file=sys.stderr)
    raise SystemExit(1)

print("zfc-canonical-slice-purity-check: OK")
PY
