#!/usr/bin/env bash
# LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
# Copyright (C) 2026 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only
# Policy:
# - The atomic LT spine modules are intentionally small and strictly layered.
# - Their allowed imports are fixed and minimal to prevent accidental meaning leaks.

set -euo pipefail

CHECK_NAME="atomic-spine-import-check"
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

ATOMIC: dict[str, set[str]] = {
    "LogOS/LT/ConPreorder.agda": {"LogOS.Prelude"},
    "LogOS/LT/FunPreorder.agda": {"LogOS.Prelude", "LogOS.LT.ConPreorder"},
    "LogOS/LT/View.agda": {"LogOS.Prelude", "LogOS.LT.ConPreorder", "LogOS.Syntax.Prop"},
    "LogOS/LT/Kernel.agda": {"LogOS.Prelude", "LogOS.LT.ConPreorder", "LogOS.LT.View"},
    "LogOS/LT/Coherence.agda": {"LogOS.Prelude", "LogOS.LT.ConPreorder"},
    "LogOS/LT/BoundaryHom.agda": {"LogOS.Prelude", "LogOS.LT.ConPreorder", "LogOS.LT.Kernel"},
    "LogOS/LT/BoundaryImplementation.agda": {
        "LogOS.LT.BoundaryImplementation.Core",
        "LogOS.LT.BoundaryImplementation.Laws",
    },
    "LogOS/LT/BoundaryImplementation/Core.agda": {
        "LogOS.Prelude",
        "LogOS.LT.ConPreorder",
        "LogOS.LT.Kernel",
        "LogOS.LT.Coherence",
        "LogOS.LT.BoundaryHom",
    },
    "LogOS/LT/Hom.agda": {
        "LogOS.LT.Hom.Core",
        "LogOS.LT.Hom.Laws",
    },
    "LogOS/LT/Hom/Core.agda": {
        "LogOS.Prelude",
        "LogOS.LT.ConPreorder",
        "LogOS.LT.FunPreorder",
        "LogOS.LT.View",
        "LogOS.LT.Kernel",
        "LogOS.LT.Coherence",
        "LogOS.LT.BoundaryHom",
        "LogOS.LT.BoundaryImplementation.Core",
    },
    "LogOS/LT/Thin2Cat.agda": {"LogOS.Prelude", "LogOS.LT.ConPreorder"},
    "LogOS/LT/Thin2Functor.agda": {"LogOS.Prelude", "LogOS.LT.ConPreorder", "LogOS.LT.Thin2Cat"},
    "LogOS/LT/DisplayedThin2Cat.agda": {
        "LogOS.LT.DisplayedThin2Cat.Core",
        "LogOS.LT.DisplayedThin2Cat.Totalisation",
        "LogOS.LT.DisplayedThin2Cat.MapDecorated",
        "LogOS.LT.DisplayedThin2Cat.Product",
    },
    "LogOS/LT/DisplayedThin2Cat/Core.agda": {
        "LogOS.Prelude",
        "LogOS.LT.ConPreorder",
        "LogOS.LT.Thin2Cat",
    },
    "LogOS/LT/DisplayedThin2Cat/Totalisation.agda": {
        "LogOS.Prelude",
        "LogOS.LT.ConPreorder",
        "LogOS.LT.Thin2Cat",
        "LogOS.LT.Thin2Functor",
        "LogOS.LT.DisplayedThin2Cat.Core",
    },
    "LogOS/LT/DisplayedThin2Cat/MapDecorated.agda": {
        "LogOS.Prelude",
        "LogOS.LT.ConPreorder",
        "LogOS.LT.Thin2Cat",
        "LogOS.LT.Thin2Functor",
        "LogOS.LT.DisplayedThin2Cat.Core",
        "LogOS.LT.DisplayedThin2Cat.Totalisation",
    },
    "LogOS/LT/DisplayedThin2Cat/Product.agda": {
        "LogOS.Prelude",
        "LogOS.LT.ConPreorder",
        "LogOS.LT.Thin2Cat",
        "LogOS.LT.Thin2Functor",
        "LogOS.LT.DisplayedThin2Cat.Core",
        "LogOS.LT.DisplayedThin2Cat.Totalisation",
    },
}


def main() -> int:
    violations: list[str] = []

    for rel, allowed in sorted(ATOMIC.items()):
        path = ROOT / rel
        if not path.is_file():
            violations.append(f"{rel}: missing file")
            continue

        for i, line in enumerate(path.read_text(encoding="utf-8").splitlines(), start=1):
            m = IMPORT_RE.match(line)
            if not m:
                continue
            dep = m.group(1)
            if dep not in allowed:
                allowed_list = ", ".join(sorted(allowed))
                violations.append(f"{rel}:{i}: forbidden import {dep} (allowed: {allowed_list})")

    if violations:
        print("atomic-spine-import-check: FAIL", file=sys.stderr)
        print(
            "Policy: the atomic LT spine modules must be strictly layered and import-minimal.",
            file=sys.stderr,
        )
        for v in violations:
            print(f"  - {v}", file=sys.stderr)
        return 1

    print("atomic-spine-import-check: OK")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
PY
