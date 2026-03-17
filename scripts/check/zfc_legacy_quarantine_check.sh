#!/usr/bin/env bash
# LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
# Copyright (C) 2026 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only
# Policy:
# - The iterative-tree legacy pair packaging is quarantined compatibility only.
# - Curated surfaces, docs, and examples must not mention it.

set -euo pipefail

CHECK_NAME="zfc-legacy-quarantine-check"
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
# shellcheck source=scripts/lib/check_common.sh
source "${SCRIPT_DIR}/lib/check_common.sh"

ROOT="$(check_repo_root "${BASH_SOURCE[0]}")"
cd "${ROOT}"

check_require_cmd "${CHECK_NAME}" python3

python3 - <<'PY'
from __future__ import annotations

import sys
from pathlib import Path

ROOT = Path(".").resolve()
ALLOW = {
    "LogOS/Apps/ZFC/Models/IterativeSetTree/CumulativeHierarchyLegacyPair.agda",
}
TOKENS = [
    "CumulativeHierarchyLegacyPair",
]

violations: list[str] = []

for base in [ROOT / "LogOS", ROOT / "docs"]:
    if not base.exists():
        continue
    for path in sorted(base.rglob("*")):
        if path.is_dir() or "_build" in path.parts:
            continue
        if "Generated" in path.parts:
            continue
        if path.suffix not in {".agda", ".md"} and not path.name.endswith(".lagda.md"):
            continue
        rel = path.relative_to(ROOT).as_posix()
        if rel in ALLOW:
            continue
        text = path.read_text(encoding="utf-8")
        for token in TOKENS:
            if token in text:
                violations.append(f"{rel}: mentions quarantined legacy surface {token}")

if violations:
    print("zfc-legacy-quarantine-check: FAIL", file=sys.stderr)
    print("Policy: the iterative-tree legacy pair surface must remain quarantined.", file=sys.stderr)
    for item in violations:
        print(f"  - {item}", file=sys.stderr)
    raise SystemExit(1)

print("zfc-legacy-quarantine-check: OK")
PY
